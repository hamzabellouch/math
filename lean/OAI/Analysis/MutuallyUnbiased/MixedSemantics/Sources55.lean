import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical95
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical170
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical192
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical198
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical199
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical201
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical202
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical203

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1760 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1760 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC1760 : Charge := ![3, -1, 1, -1, 0, -2]
def sourceForm1760 : Integer.Sparse Master := [(Sum.inr 567, 1), (Sum.inr 878, 1), (Sum.inr 977, 2), (Sum.inr 998, 1), (Sum.inr 1004, 1), (Sum.inr 4080, -1)]

theorem sourceEq1760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1760 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1760 + difference 1 0) (sourceB1760 + difference 0 1) sourceC1760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 567) := by
    have ha : (tripleCharges (sourceA1760 + difference 1 0) (sourceB1760 + difference 0 1) sourceC1760) = raw25556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1760 sourceB1760 sourceC1760 difference raw25556; decide +kernel
    rw [ha]
    exact (canonical25556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1760 + difference 1 1) (sourceB1760 + difference 1 1) sourceC1760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1760 + difference 1 1) (sourceB1760 + difference 1 1) sourceC1760) = raw25549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1760 sourceB1760 sourceC1760 difference raw25549; decide +kernel
    rw [ha]
    exact (canonical25549 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1760 + difference 1 2) (sourceB1760 + difference 2 1) sourceC1760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 878) := by
    have ha : (tripleCharges (sourceA1760 + difference 1 2) (sourceB1760 + difference 2 1) sourceC1760) = raw25557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1760 sourceB1760 sourceC1760 difference raw25557; decide +kernel
    rw [ha]
    exact (canonical25557 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1760 + difference 1 3) (sourceB1760 + difference 3 1) sourceC1760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1760 + difference 1 3) (sourceB1760 + difference 3 1) sourceC1760) = raw25558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1760 sourceB1760 sourceC1760 difference raw25558; decide +kernel
    rw [ha]
    exact (canonical25558 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1760 + difference 1 4) (sourceB1760 + difference 4 1) sourceC1760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1004) := by
    have ha : (tripleCharges (sourceA1760 + difference 1 4) (sourceB1760 + difference 4 1) sourceC1760) = raw25559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1760 sourceB1760 sourceC1760 difference raw25559; decide +kernel
    rw [ha]
    exact (canonical25559 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1760 + difference 1 5) (sourceB1760 + difference 5 1) sourceC1760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1760 + difference 1 5) (sourceB1760 + difference 5 1) sourceC1760) = raw25560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1760 sourceB1760 sourceC1760 difference raw25560; decide +kernel
    rw [ha]
    exact (canonical25560 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1760 + sourceB1760) sourceC1760) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1760 + sourceB1760) sourceC1760) = raw25555 := by
      apply Matrix.ext; unfold doubleCharges sourceA1760 sourceB1760 sourceC1760 raw25555; decide +kernel
    rw [ha]
    exact (canonical25555 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1760 sourceB1760 sourceC1760
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1760, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1761 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1761 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC1761 : Charge := ![3, -1, 1, -1, 0, -2]
def sourceForm1761 : Integer.Sparse Master := [(Sum.inr 865, 1), (Sum.inr 866, 1), (Sum.inr 869, 1), (Sum.inr 878, 1), (Sum.inr 977, 1), (Sum.inr 1908, 1), (Sum.inr 4080, -1)]

theorem sourceEq1761 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1761 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1761 + difference 0 2) (sourceB1761 + difference 2 0) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1908) := by
    have ha : (tripleCharges (sourceA1761 + difference 0 2) (sourceB1761 + difference 2 0) sourceC1761) = raw25551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25551; decide +kernel
    rw [ha]
    exact (canonical25551 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1761 + difference 1 2) (sourceB1761 + difference 2 1) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 878) := by
    have ha : (tripleCharges (sourceA1761 + difference 1 2) (sourceB1761 + difference 2 1) sourceC1761) = raw25557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25557; decide +kernel
    rw [ha]
    exact (canonical25557 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1761 + difference 2 2) (sourceB1761 + difference 2 2) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1761 + difference 2 2) (sourceB1761 + difference 2 2) sourceC1761) = raw25549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25549; decide +kernel
    rw [ha]
    exact (canonical25549 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1761 + difference 3 2) (sourceB1761 + difference 2 3) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA1761 + difference 3 2) (sourceB1761 + difference 2 3) sourceC1761) = raw25561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25561; decide +kernel
    rw [ha]
    exact (canonical25561 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1761 + difference 4 2) (sourceB1761 + difference 2 4) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 869) := by
    have ha : (tripleCharges (sourceA1761 + difference 4 2) (sourceB1761 + difference 2 4) sourceC1761) = raw25562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25562; decide +kernel
    rw [ha]
    exact (canonical25562 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1761 + difference 5 2) (sourceB1761 + difference 2 5) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 865) := by
    have ha : (tripleCharges (sourceA1761 + difference 5 2) (sourceB1761 + difference 2 5) sourceC1761) = raw25563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25563; decide +kernel
    rw [ha]
    exact (canonical25563 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1761 + sourceB1761) sourceC1761) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1761 + sourceB1761) sourceC1761) = raw25555 := by
      apply Matrix.ext; unfold doubleCharges sourceA1761 sourceB1761 sourceC1761 raw25555; decide +kernel
    rw [ha]
    exact (canonical25555 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1761 sourceB1761 sourceC1761
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1761, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1762 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceB1762 : Charge := ![3, -1, 1, -1, 0, -2]
def sourceC1762 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1762 : Integer.Sparse Master := [(Sum.inr 699, 1), (Sum.inr 700, 1), (Sum.inr 703, 1), (Sum.inr 712, 1), (Sum.inr 806, 1), (Sum.inr 1597, 1), (Sum.inr 4069, -1)]

theorem sourceEq1762 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1762 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1762 + difference 0 0) (sourceB1762 + difference 0 0) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1762 + difference 0 0) (sourceB1762 + difference 0 0) sourceC1762) = raw25548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25548; decide +kernel
    rw [ha]
    exact (canonical25548 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1762 + difference 1 0) (sourceB1762 + difference 0 1) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 703) := by
    have ha : (tripleCharges (sourceA1762 + difference 1 0) (sourceB1762 + difference 0 1) sourceC1762) = raw25564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25564; decide +kernel
    rw [ha]
    exact (canonical25564 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1762 + difference 2 0) (sourceB1762 + difference 0 2) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1762 + difference 2 0) (sourceB1762 + difference 0 2) sourceC1762) = raw25350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25350; decide +kernel
    rw [ha]
    exact (canonical25350 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1762 + difference 3 0) (sourceB1762 + difference 0 3) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 700) := by
    have ha : (tripleCharges (sourceA1762 + difference 3 0) (sourceB1762 + difference 0 3) sourceC1762) = raw25565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25565; decide +kernel
    rw [ha]
    exact (canonical25565 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1762 + difference 4 0) (sourceB1762 + difference 0 4) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 712) := by
    have ha : (tripleCharges (sourceA1762 + difference 4 0) (sourceB1762 + difference 0 4) sourceC1762) = raw25546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25546; decide +kernel
    rw [ha]
    exact (canonical25546 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1762 + difference 5 0) (sourceB1762 + difference 0 5) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 699) := by
    have ha : (tripleCharges (sourceA1762 + difference 5 0) (sourceB1762 + difference 0 5) sourceC1762) = raw25566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25566; decide +kernel
    rw [ha]
    exact (canonical25566 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1762 + sourceB1762) sourceC1762) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1762 + sourceB1762) sourceC1762) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1762 sourceB1762 sourceC1762 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1762 sourceB1762 sourceC1762
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1762, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1763 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1763 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1763 : Charge := ![3, -1, 1, 0, 0, -3]
def sourceForm1763 : Integer.Sparse Master := [(Sum.inr 976, 1), (Sum.inr 1907, 1), (Sum.inr 2074, 1), (Sum.inr 2201, 1), (Sum.inr 2203, 2), (Sum.inr 4081, -1)]

theorem sourceEq1763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1763 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 0) (sourceB1763 + difference 0 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 976) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 0) (sourceB1763 + difference 0 0) sourceC1763) = raw25567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25567; decide +kernel
    rw [ha]
    exact (canonical25567 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 1) (sourceB1763 + difference 1 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2074) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 1) (sourceB1763 + difference 1 0) sourceC1763) = raw25568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25568; decide +kernel
    rw [ha]
    exact (canonical25568 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 2) (sourceB1763 + difference 2 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1907) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 2) (sourceB1763 + difference 2 0) sourceC1763) = raw25569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25569; decide +kernel
    rw [ha]
    exact (canonical25569 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 3) (sourceB1763 + difference 3 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 3) (sourceB1763 + difference 3 0) sourceC1763) = raw25570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25570; decide +kernel
    rw [ha]
    exact (canonical25570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 4) (sourceB1763 + difference 4 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 4) (sourceB1763 + difference 4 0) sourceC1763) = raw25571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25571; decide +kernel
    rw [ha]
    exact (canonical25571 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 5) (sourceB1763 + difference 5 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 5) (sourceB1763 + difference 5 0) sourceC1763) = raw25572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25572; decide +kernel
    rw [ha]
    exact (canonical25572 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1763 + sourceB1763) sourceC1763) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1763 + sourceB1763) sourceC1763) = raw25573 := by
      apply Matrix.ext; unfold doubleCharges sourceA1763 sourceB1763 sourceC1763 raw25573; decide +kernel
    rw [ha]
    exact (canonical25573 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1763 sourceB1763 sourceC1763
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1763, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1764 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1764 : Charge := ![1, 0, 0, 2, 0, -3]
def sourceC1764 : Charge := ![3, 0, 0, -3, -1, 1]
def sourceForm1764 : Integer.Sparse Master := [(Sum.inr 1088, 1), (Sum.inr 2059, 2), (Sum.inr 2222, 1), (Sum.inr 2267, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

theorem sourceEq1764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1764 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1764 + difference 0 0) (sourceB1764 + difference 0 0) sourceC1764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1088) := by
    have ha : (tripleCharges (sourceA1764 + difference 0 0) (sourceB1764 + difference 0 0) sourceC1764) = raw25574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1764 sourceB1764 sourceC1764 difference raw25574; decide +kernel
    rw [ha]
    exact (canonical25574 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1764 + difference 0 1) (sourceB1764 + difference 1 0) sourceC1764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2059) := by
    have ha : (tripleCharges (sourceA1764 + difference 0 1) (sourceB1764 + difference 1 0) sourceC1764) = raw25575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1764 sourceB1764 sourceC1764 difference raw25575; decide +kernel
    rw [ha]
    exact (canonical25575 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1764 + difference 0 2) (sourceB1764 + difference 2 0) sourceC1764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2059) := by
    have ha : (tripleCharges (sourceA1764 + difference 0 2) (sourceB1764 + difference 2 0) sourceC1764) = raw25576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1764 sourceB1764 sourceC1764 difference raw25576; decide +kernel
    rw [ha]
    exact (canonical25576 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1764 + difference 0 3) (sourceB1764 + difference 3 0) sourceC1764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA1764 + difference 0 3) (sourceB1764 + difference 3 0) sourceC1764) = raw25577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1764 sourceB1764 sourceC1764 difference raw25577; decide +kernel
    rw [ha]
    exact (canonical25577 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1764 + difference 0 4) (sourceB1764 + difference 4 0) sourceC1764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA1764 + difference 0 4) (sourceB1764 + difference 4 0) sourceC1764) = raw25578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1764 sourceB1764 sourceC1764 difference raw25578; decide +kernel
    rw [ha]
    exact (canonical25578 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1764 + difference 0 5) (sourceB1764 + difference 5 0) sourceC1764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1764 + difference 0 5) (sourceB1764 + difference 5 0) sourceC1764) = raw25579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1764 sourceB1764 sourceC1764 difference raw25579; decide +kernel
    rw [ha]
    exact (canonical25579 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1764 + sourceB1764) sourceC1764) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1764 + sourceB1764) sourceC1764) = raw25580 := by
      apply Matrix.ext; unfold doubleCharges sourceA1764 sourceB1764 sourceC1764 raw25580; decide +kernel
    rw [ha]
    exact (canonical25580 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1764 sourceB1764 sourceC1764
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1764, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1765 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1765 : Charge := ![1, 0, 0, 2, 0, -3]
def sourceC1765 : Charge := ![3, 0, 0, -3, -1, 1]
def sourceForm1765 : Integer.Sparse Master := [(Sum.inr 1070, 2), (Sum.inr 1074, 1), (Sum.inr 1076, 1), (Sum.inr 1088, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

theorem sourceEq1765 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1765 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1765 + difference 0 5) (sourceB1765 + difference 5 0) sourceC1765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1765 + difference 0 5) (sourceB1765 + difference 5 0) sourceC1765) = raw25579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1765 sourceB1765 sourceC1765 difference raw25579; decide +kernel
    rw [ha]
    exact (canonical25579 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1765 + difference 1 5) (sourceB1765 + difference 5 1) sourceC1765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1070) := by
    have ha : (tripleCharges (sourceA1765 + difference 1 5) (sourceB1765 + difference 5 1) sourceC1765) = raw25581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1765 sourceB1765 sourceC1765 difference raw25581; decide +kernel
    rw [ha]
    exact (canonical25581 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1765 + difference 2 5) (sourceB1765 + difference 5 2) sourceC1765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1070) := by
    have ha : (tripleCharges (sourceA1765 + difference 2 5) (sourceB1765 + difference 5 2) sourceC1765) = raw25582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1765 sourceB1765 sourceC1765 difference raw25582; decide +kernel
    rw [ha]
    exact (canonical25582 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1765 + difference 3 5) (sourceB1765 + difference 5 3) sourceC1765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1765 + difference 3 5) (sourceB1765 + difference 5 3) sourceC1765) = raw25583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1765 sourceB1765 sourceC1765 difference raw25583; decide +kernel
    rw [ha]
    exact (canonical25583 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1765 + difference 4 5) (sourceB1765 + difference 5 4) sourceC1765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1076) := by
    have ha : (tripleCharges (sourceA1765 + difference 4 5) (sourceB1765 + difference 5 4) sourceC1765) = raw25584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1765 sourceB1765 sourceC1765 difference raw25584; decide +kernel
    rw [ha]
    exact (canonical25584 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1765 + difference 5 5) (sourceB1765 + difference 5 5) sourceC1765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1088) := by
    have ha : (tripleCharges (sourceA1765 + difference 5 5) (sourceB1765 + difference 5 5) sourceC1765) = raw25574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1765 sourceB1765 sourceC1765 difference raw25574; decide +kernel
    rw [ha]
    exact (canonical25574 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1765 + sourceB1765) sourceC1765) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1765 + sourceB1765) sourceC1765) = raw25580 := by
      apply Matrix.ext; unfold doubleCharges sourceA1765 sourceB1765 sourceC1765 raw25580; decide +kernel
    rw [ha]
    exact (canonical25580 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1765 sourceB1765 sourceC1765
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1765, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1766 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1766 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC1766 : Charge := ![3, 0, 0, -3, 1, -1]
def sourceForm1766 : Integer.Sparse Master := [(Sum.inr 1076, 1), (Sum.inr 2049, 2), (Sum.inr 2230, 1), (Sum.inr 2282, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

theorem sourceEq1766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1766 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 0) (sourceB1766 + difference 0 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1076) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 0) (sourceB1766 + difference 0 0) sourceC1766) = raw25585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25585; decide +kernel
    rw [ha]
    exact (canonical25585 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 1) (sourceB1766 + difference 1 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2049) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 1) (sourceB1766 + difference 1 0) sourceC1766) = raw25586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25586; decide +kernel
    rw [ha]
    exact (canonical25586 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 2) (sourceB1766 + difference 2 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2049) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 2) (sourceB1766 + difference 2 0) sourceC1766) = raw25587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25587; decide +kernel
    rw [ha]
    exact (canonical25587 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 3) (sourceB1766 + difference 3 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2282) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 3) (sourceB1766 + difference 3 0) sourceC1766) = raw25588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25588; decide +kernel
    rw [ha]
    exact (canonical25588 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 4) (sourceB1766 + difference 4 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 4) (sourceB1766 + difference 4 0) sourceC1766) = raw25589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25589; decide +kernel
    rw [ha]
    exact (canonical25589 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1766 + difference 0 5) (sourceB1766 + difference 5 0) sourceC1766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1766 + difference 0 5) (sourceB1766 + difference 5 0) sourceC1766) = raw25590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1766 sourceB1766 sourceC1766 difference raw25590; decide +kernel
    rw [ha]
    exact (canonical25590 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1766 + sourceB1766) sourceC1766) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1766 + sourceB1766) sourceC1766) = raw25591 := by
      apply Matrix.ext; unfold doubleCharges sourceA1766 sourceB1766 sourceC1766 raw25591; decide +kernel
    rw [ha]
    exact (canonical25591 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1766 sourceB1766 sourceC1766
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1766, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1767 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1767 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC1767 : Charge := ![3, 0, 0, -2, -2, 1]
def sourceForm1767 : Integer.Sparse Master := [(Sum.inr 1090, 1), (Sum.inr 2061, 2), (Sum.inr 2280, 2), (Sum.inr 2288, 1), (Sum.inr 4082, -1)]

theorem sourceEq1767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1767 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1767 + difference 0 0) (sourceB1767 + difference 0 0) sourceC1767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1090) := by
    have ha : (tripleCharges (sourceA1767 + difference 0 0) (sourceB1767 + difference 0 0) sourceC1767) = raw25592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1767 sourceB1767 sourceC1767 difference raw25592; decide +kernel
    rw [ha]
    exact (canonical25592 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1767 + difference 0 1) (sourceB1767 + difference 1 0) sourceC1767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2061) := by
    have ha : (tripleCharges (sourceA1767 + difference 0 1) (sourceB1767 + difference 1 0) sourceC1767) = raw25593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1767 sourceB1767 sourceC1767 difference raw25593; decide +kernel
    rw [ha]
    exact (canonical25593 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1767 + difference 0 2) (sourceB1767 + difference 2 0) sourceC1767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2061) := by
    have ha : (tripleCharges (sourceA1767 + difference 0 2) (sourceB1767 + difference 2 0) sourceC1767) = raw25594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1767 sourceB1767 sourceC1767 difference raw25594; decide +kernel
    rw [ha]
    exact (canonical25594 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1767 + difference 0 3) (sourceB1767 + difference 3 0) sourceC1767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA1767 + difference 0 3) (sourceB1767 + difference 3 0) sourceC1767) = raw25595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1767 sourceB1767 sourceC1767 difference raw25595; decide +kernel
    rw [ha]
    exact (canonical25595 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1767 + difference 0 4) (sourceB1767 + difference 4 0) sourceC1767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA1767 + difference 0 4) (sourceB1767 + difference 4 0) sourceC1767) = raw25596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1767 sourceB1767 sourceC1767 difference raw25596; decide +kernel
    rw [ha]
    exact (canonical25596 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1767 + difference 0 5) (sourceB1767 + difference 5 0) sourceC1767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA1767 + difference 0 5) (sourceB1767 + difference 5 0) sourceC1767) = raw25597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1767 sourceB1767 sourceC1767 difference raw25597; decide +kernel
    rw [ha]
    exact (canonical25597 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1767 + sourceB1767) sourceC1767) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1767 + sourceB1767) sourceC1767) = raw25598 := by
      apply Matrix.ext; unfold doubleCharges sourceA1767 sourceB1767 sourceC1767 raw25598; decide +kernel
    rw [ha]
    exact (canonical25598 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1767 sourceB1767 sourceC1767
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1767, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1768 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1768 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC1768 : Charge := ![3, 0, 0, -2, -2, 1]
def sourceForm1768 : Integer.Sparse Master := [(Sum.inr 1071, 2), (Sum.inr 1075, 2), (Sum.inr 1090, 1), (Sum.inr 2288, 1), (Sum.inr 4082, -1)]

theorem sourceEq1768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1768 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1768 + difference 0 5) (sourceB1768 + difference 5 0) sourceC1768) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA1768 + difference 0 5) (sourceB1768 + difference 5 0) sourceC1768) = raw25597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1768 sourceB1768 sourceC1768 difference raw25597; decide +kernel
    rw [ha]
    exact (canonical25597 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1768 + difference 1 5) (sourceB1768 + difference 5 1) sourceC1768) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1071) := by
    have ha : (tripleCharges (sourceA1768 + difference 1 5) (sourceB1768 + difference 5 1) sourceC1768) = raw25599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1768 sourceB1768 sourceC1768 difference raw25599; decide +kernel
    rw [ha]
    exact (canonical25599 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1768 + difference 2 5) (sourceB1768 + difference 5 2) sourceC1768) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1071) := by
    have ha : (tripleCharges (sourceA1768 + difference 2 5) (sourceB1768 + difference 5 2) sourceC1768) = raw25600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1768 sourceB1768 sourceC1768 difference raw25600; decide +kernel
    rw [ha]
    exact (canonical25600 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1768 + difference 3 5) (sourceB1768 + difference 5 3) sourceC1768) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1768 + difference 3 5) (sourceB1768 + difference 5 3) sourceC1768) = raw25601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1768 sourceB1768 sourceC1768 difference raw25601; decide +kernel
    rw [ha]
    exact (canonical25601 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1768 + difference 4 5) (sourceB1768 + difference 5 4) sourceC1768) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1768 + difference 4 5) (sourceB1768 + difference 5 4) sourceC1768) = raw25602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1768 sourceB1768 sourceC1768 difference raw25602; decide +kernel
    rw [ha]
    exact (canonical25602 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1768 + difference 5 5) (sourceB1768 + difference 5 5) sourceC1768) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1090) := by
    have ha : (tripleCharges (sourceA1768 + difference 5 5) (sourceB1768 + difference 5 5) sourceC1768) = raw25592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1768 sourceB1768 sourceC1768 difference raw25592; decide +kernel
    rw [ha]
    exact (canonical25592 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1768 + sourceB1768) sourceC1768) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1768 + sourceB1768) sourceC1768) = raw25598 := by
      apply Matrix.ext; unfold doubleCharges sourceA1768 sourceB1768 sourceC1768 raw25598; decide +kernel
    rw [ha]
    exact (canonical25598 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1768 sourceB1768 sourceC1768
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1768, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1769 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1769 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1769 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceForm1769 : Integer.Sparse Master := [(Sum.inr 4176, 2), (Sum.inr 4184, 1), (Sum.inr 4185, 1), (Sum.inr 4188, 1), (Sum.inr 4345, 2), (Sum.inr 4353, 2), (Sum.inr 4354, 2), (Sum.inr 4357, 2), (Sum.inr 4459, 2), (Sum.inr 4464, 1), (Sum.inr 4466, 1), (Sum.inr 4475, 2), (Sum.inr 4478, 1), (Sum.inr 4480, 1), (Sum.inr 4495, 2), (Sum.inr 4498, 1), (Sum.inr 4499, 1), (Sum.inr 4839, 2), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4898, 1)]

theorem sourceEq1769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1769 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1769 + difference 0 1) (sourceB1769 + difference 1 0) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA1769 + difference 0 1) (sourceB1769 + difference 1 0) sourceC1769) = raw25603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25603; decide +kernel
    rw [ha]
    exact (canonical25603 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1769 + difference 0 2) (sourceB1769 + difference 2 0) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA1769 + difference 0 2) (sourceB1769 + difference 2 0) sourceC1769) = raw25604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25604; decide +kernel
    rw [ha]
    exact (canonical25604 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1769 + difference 0 3) (sourceB1769 + difference 3 0) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA1769 + difference 0 3) (sourceB1769 + difference 3 0) sourceC1769) = raw25605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25605; decide +kernel
    rw [ha]
    exact (canonical25605 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1769 + difference 0 4) (sourceB1769 + difference 4 0) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA1769 + difference 0 4) (sourceB1769 + difference 4 0) sourceC1769) = raw25606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25606; decide +kernel
    rw [ha]
    exact (canonical25606 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1769 + difference 0 5) (sourceB1769 + difference 5 0) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1769 + difference 0 5) (sourceB1769 + difference 5 0) sourceC1769) = raw25607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25607; decide +kernel
    rw [ha]
    exact (canonical25607 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1769 + difference 1 0) (sourceB1769 + difference 0 1) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4176) := by
    have ha : (tripleCharges (sourceA1769 + difference 1 0) (sourceB1769 + difference 0 1) sourceC1769) = raw25608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25608; decide +kernel
    rw [ha]
    exact (canonical25608 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1769 + difference 1 2) (sourceB1769 + difference 2 1) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4345) := by
    have ha : (tripleCharges (sourceA1769 + difference 1 2) (sourceB1769 + difference 2 1) sourceC1769) = raw25609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25609; decide +kernel
    rw [ha]
    exact (canonical25609 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1769 + difference 1 3) (sourceB1769 + difference 3 1) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA1769 + difference 1 3) (sourceB1769 + difference 3 1) sourceC1769) = raw25610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25610; decide +kernel
    rw [ha]
    exact (canonical25610 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1769 + difference 1 4) (sourceB1769 + difference 4 1) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1769 + difference 1 4) (sourceB1769 + difference 4 1) sourceC1769) = raw25611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25611; decide +kernel
    rw [ha]
    exact (canonical25611 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1769 + difference 1 5) (sourceB1769 + difference 5 1) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1769 + difference 1 5) (sourceB1769 + difference 5 1) sourceC1769) = raw25612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25612; decide +kernel
    rw [ha]
    exact (canonical25612 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1769 + difference 2 0) (sourceB1769 + difference 0 2) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4176) := by
    have ha : (tripleCharges (sourceA1769 + difference 2 0) (sourceB1769 + difference 0 2) sourceC1769) = raw25613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25613; decide +kernel
    rw [ha]
    exact (canonical25613 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1769 + difference 2 1) (sourceB1769 + difference 1 2) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4345) := by
    have ha : (tripleCharges (sourceA1769 + difference 2 1) (sourceB1769 + difference 1 2) sourceC1769) = raw25614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25614; decide +kernel
    rw [ha]
    exact (canonical25614 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1769 + difference 2 3) (sourceB1769 + difference 3 2) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA1769 + difference 2 3) (sourceB1769 + difference 3 2) sourceC1769) = raw25615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25615; decide +kernel
    rw [ha]
    exact (canonical25615 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1769 + difference 2 4) (sourceB1769 + difference 4 2) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1769 + difference 2 4) (sourceB1769 + difference 4 2) sourceC1769) = raw25616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25616; decide +kernel
    rw [ha]
    exact (canonical25616 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1769 + difference 2 5) (sourceB1769 + difference 5 2) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1769 + difference 2 5) (sourceB1769 + difference 5 2) sourceC1769) = raw25617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25617; decide +kernel
    rw [ha]
    exact (canonical25617 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1769 + difference 3 0) (sourceB1769 + difference 0 3) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4185) := by
    have ha : (tripleCharges (sourceA1769 + difference 3 0) (sourceB1769 + difference 0 3) sourceC1769) = raw25618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25618; decide +kernel
    rw [ha]
    exact (canonical25618 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1769 + difference 3 1) (sourceB1769 + difference 1 3) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1769 + difference 3 1) (sourceB1769 + difference 1 3) sourceC1769) = raw25619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25619; decide +kernel
    rw [ha]
    exact (canonical25619 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1769 + difference 3 2) (sourceB1769 + difference 2 3) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1769 + difference 3 2) (sourceB1769 + difference 2 3) sourceC1769) = raw25620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25620; decide +kernel
    rw [ha]
    exact (canonical25620 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1769 + difference 3 4) (sourceB1769 + difference 4 3) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1769 + difference 3 4) (sourceB1769 + difference 4 3) sourceC1769) = raw25621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25621; decide +kernel
    rw [ha]
    exact (canonical25621 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1769 + difference 3 5) (sourceB1769 + difference 5 3) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1769 + difference 3 5) (sourceB1769 + difference 5 3) sourceC1769) = raw25622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25622; decide +kernel
    rw [ha]
    exact (canonical25622 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1769 + difference 4 0) (sourceB1769 + difference 0 4) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4188) := by
    have ha : (tripleCharges (sourceA1769 + difference 4 0) (sourceB1769 + difference 0 4) sourceC1769) = raw25623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25623; decide +kernel
    rw [ha]
    exact (canonical25623 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1769 + difference 4 1) (sourceB1769 + difference 1 4) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA1769 + difference 4 1) (sourceB1769 + difference 1 4) sourceC1769) = raw25624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25624; decide +kernel
    rw [ha]
    exact (canonical25624 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1769 + difference 4 2) (sourceB1769 + difference 2 4) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA1769 + difference 4 2) (sourceB1769 + difference 2 4) sourceC1769) = raw25625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25625; decide +kernel
    rw [ha]
    exact (canonical25625 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1769 + difference 4 3) (sourceB1769 + difference 3 4) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA1769 + difference 4 3) (sourceB1769 + difference 3 4) sourceC1769) = raw25626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25626; decide +kernel
    rw [ha]
    exact (canonical25626 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1769 + difference 4 5) (sourceB1769 + difference 5 4) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1769 + difference 4 5) (sourceB1769 + difference 5 4) sourceC1769) = raw25627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25627; decide +kernel
    rw [ha]
    exact (canonical25627 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1769 + difference 5 0) (sourceB1769 + difference 0 5) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4184) := by
    have ha : (tripleCharges (sourceA1769 + difference 5 0) (sourceB1769 + difference 0 5) sourceC1769) = raw25628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25628; decide +kernel
    rw [ha]
    exact (canonical25628 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1769 + difference 5 1) (sourceB1769 + difference 1 5) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4353) := by
    have ha : (tripleCharges (sourceA1769 + difference 5 1) (sourceB1769 + difference 1 5) sourceC1769) = raw25629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25629; decide +kernel
    rw [ha]
    exact (canonical25629 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1769 + difference 5 2) (sourceB1769 + difference 2 5) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4353) := by
    have ha : (tripleCharges (sourceA1769 + difference 5 2) (sourceB1769 + difference 2 5) sourceC1769) = raw25630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25630; decide +kernel
    rw [ha]
    exact (canonical25630 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1769 + difference 5 3) (sourceB1769 + difference 3 5) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA1769 + difference 5 3) (sourceB1769 + difference 3 5) sourceC1769) = raw25631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25631; decide +kernel
    rw [ha]
    exact (canonical25631 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1769 + difference 5 4) (sourceB1769 + difference 4 5) sourceC1769) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1769 + difference 5 4) (sourceB1769 + difference 4 5) sourceC1769) = raw25632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1769 sourceB1769 sourceC1769 difference raw25632; decide +kernel
    rw [ha]
    exact (canonical25632 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1769 sourceB1769 sourceC1769
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1769, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1770 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1770 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1770 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceForm1770 : Integer.Sparse Master := [(Sum.inr 1512, 2), (Sum.inr 1525, 1), (Sum.inr 1526, 1), (Sum.inr 1530, 1), (Sum.inr 1668, 2), (Sum.inr 1681, 2), (Sum.inr 1682, 2), (Sum.inr 1686, 2), (Sum.inr 1708, 2), (Sum.inr 1714, 2), (Sum.inr 1715, 2), (Sum.inr 1727, 1), (Sum.inr 1728, 1), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 1745, 1), (Sum.inr 1746, 1), (Sum.inr 2216, 2), (Sum.inr 2265, 1), (Sum.inr 2278, 1), (Sum.inr 2279, 1)]

theorem sourceEq1770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1770 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1770 + difference 0 1) (sourceB1770 + difference 1 0) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1770 + difference 0 1) (sourceB1770 + difference 1 0) sourceC1770) = raw25633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25633; decide +kernel
    rw [ha]
    exact (canonical25633 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1770 + difference 0 2) (sourceB1770 + difference 2 0) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1770 + difference 0 2) (sourceB1770 + difference 2 0) sourceC1770) = raw25634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25634; decide +kernel
    rw [ha]
    exact (canonical25634 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1770 + difference 0 3) (sourceB1770 + difference 3 0) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA1770 + difference 0 3) (sourceB1770 + difference 3 0) sourceC1770) = raw25635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25635; decide +kernel
    rw [ha]
    exact (canonical25635 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1770 + difference 0 4) (sourceB1770 + difference 4 0) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA1770 + difference 0 4) (sourceB1770 + difference 4 0) sourceC1770) = raw25636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25636; decide +kernel
    rw [ha]
    exact (canonical25636 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1770 + difference 0 5) (sourceB1770 + difference 5 0) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA1770 + difference 0 5) (sourceB1770 + difference 5 0) sourceC1770) = raw25637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25637; decide +kernel
    rw [ha]
    exact (canonical25637 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1770 + difference 1 0) (sourceB1770 + difference 0 1) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1770 + difference 1 0) (sourceB1770 + difference 0 1) sourceC1770) = raw25638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25638; decide +kernel
    rw [ha]
    exact (canonical25638 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1770 + difference 1 2) (sourceB1770 + difference 2 1) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA1770 + difference 1 2) (sourceB1770 + difference 2 1) sourceC1770) = raw25639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25639; decide +kernel
    rw [ha]
    exact (canonical25639 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1770 + difference 1 3) (sourceB1770 + difference 3 1) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1770 + difference 1 3) (sourceB1770 + difference 3 1) sourceC1770) = raw25640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25640; decide +kernel
    rw [ha]
    exact (canonical25640 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1770 + difference 1 4) (sourceB1770 + difference 4 1) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1770 + difference 1 4) (sourceB1770 + difference 4 1) sourceC1770) = raw25641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25641; decide +kernel
    rw [ha]
    exact (canonical25641 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1770 + difference 1 5) (sourceB1770 + difference 5 1) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1770 + difference 1 5) (sourceB1770 + difference 5 1) sourceC1770) = raw25642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25642; decide +kernel
    rw [ha]
    exact (canonical25642 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1770 + difference 2 0) (sourceB1770 + difference 0 2) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1770 + difference 2 0) (sourceB1770 + difference 0 2) sourceC1770) = raw25643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25643; decide +kernel
    rw [ha]
    exact (canonical25643 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1770 + difference 2 1) (sourceB1770 + difference 1 2) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA1770 + difference 2 1) (sourceB1770 + difference 1 2) sourceC1770) = raw25644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25644; decide +kernel
    rw [ha]
    exact (canonical25644 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1770 + difference 2 3) (sourceB1770 + difference 3 2) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1770 + difference 2 3) (sourceB1770 + difference 3 2) sourceC1770) = raw25645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25645; decide +kernel
    rw [ha]
    exact (canonical25645 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1770 + difference 2 4) (sourceB1770 + difference 4 2) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1770 + difference 2 4) (sourceB1770 + difference 4 2) sourceC1770) = raw25646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25646; decide +kernel
    rw [ha]
    exact (canonical25646 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1770 + difference 2 5) (sourceB1770 + difference 5 2) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1770 + difference 2 5) (sourceB1770 + difference 5 2) sourceC1770) = raw25647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25647; decide +kernel
    rw [ha]
    exact (canonical25647 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1770 + difference 3 0) (sourceB1770 + difference 0 3) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA1770 + difference 3 0) (sourceB1770 + difference 0 3) sourceC1770) = raw25648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25648; decide +kernel
    rw [ha]
    exact (canonical25648 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1770 + difference 3 1) (sourceB1770 + difference 1 3) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA1770 + difference 3 1) (sourceB1770 + difference 1 3) sourceC1770) = raw25649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25649; decide +kernel
    rw [ha]
    exact (canonical25649 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1770 + difference 3 2) (sourceB1770 + difference 2 3) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA1770 + difference 3 2) (sourceB1770 + difference 2 3) sourceC1770) = raw25650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25650; decide +kernel
    rw [ha]
    exact (canonical25650 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1770 + difference 3 4) (sourceB1770 + difference 4 3) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1770 + difference 3 4) (sourceB1770 + difference 4 3) sourceC1770) = raw25651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25651; decide +kernel
    rw [ha]
    exact (canonical25651 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1770 + difference 3 5) (sourceB1770 + difference 5 3) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1770 + difference 3 5) (sourceB1770 + difference 5 3) sourceC1770) = raw25652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25652; decide +kernel
    rw [ha]
    exact (canonical25652 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1770 + difference 4 0) (sourceB1770 + difference 0 4) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1526) := by
    have ha : (tripleCharges (sourceA1770 + difference 4 0) (sourceB1770 + difference 0 4) sourceC1770) = raw25653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25653; decide +kernel
    rw [ha]
    exact (canonical25653 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1770 + difference 4 1) (sourceB1770 + difference 1 4) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA1770 + difference 4 1) (sourceB1770 + difference 1 4) sourceC1770) = raw25654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25654; decide +kernel
    rw [ha]
    exact (canonical25654 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1770 + difference 4 2) (sourceB1770 + difference 2 4) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA1770 + difference 4 2) (sourceB1770 + difference 2 4) sourceC1770) = raw25655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25655; decide +kernel
    rw [ha]
    exact (canonical25655 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1770 + difference 4 3) (sourceB1770 + difference 3 4) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1770 + difference 4 3) (sourceB1770 + difference 3 4) sourceC1770) = raw25656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25656; decide +kernel
    rw [ha]
    exact (canonical25656 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1770 + difference 4 5) (sourceB1770 + difference 5 4) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1770 + difference 4 5) (sourceB1770 + difference 5 4) sourceC1770) = raw25657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25657; decide +kernel
    rw [ha]
    exact (canonical25657 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1770 + difference 5 0) (sourceB1770 + difference 0 5) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA1770 + difference 5 0) (sourceB1770 + difference 0 5) sourceC1770) = raw25658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25658; decide +kernel
    rw [ha]
    exact (canonical25658 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1770 + difference 5 1) (sourceB1770 + difference 1 5) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA1770 + difference 5 1) (sourceB1770 + difference 1 5) sourceC1770) = raw25659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25659; decide +kernel
    rw [ha]
    exact (canonical25659 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1770 + difference 5 2) (sourceB1770 + difference 2 5) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA1770 + difference 5 2) (sourceB1770 + difference 2 5) sourceC1770) = raw25660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25660; decide +kernel
    rw [ha]
    exact (canonical25660 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1770 + difference 5 3) (sourceB1770 + difference 3 5) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA1770 + difference 5 3) (sourceB1770 + difference 3 5) sourceC1770) = raw25661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25661; decide +kernel
    rw [ha]
    exact (canonical25661 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1770 + difference 5 4) (sourceB1770 + difference 4 5) sourceC1770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1770 + difference 5 4) (sourceB1770 + difference 4 5) sourceC1770) = raw25662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1770 sourceB1770 sourceC1770 difference raw25662; decide +kernel
    rw [ha]
    exact (canonical25662 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1770 sourceB1770 sourceC1770
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1770, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1771 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1771 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1771 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceForm1771 : Integer.Sparse Master := [(Sum.inr 4126, 2), (Sum.inr 4128, 1), (Sum.inr 4129, 1), (Sum.inr 4132, 1), (Sum.inr 4307, 2), (Sum.inr 4309, 2), (Sum.inr 4310, 2), (Sum.inr 4313, 2), (Sum.inr 4461, 2), (Sum.inr 4463, 1), (Sum.inr 4466, 1), (Sum.inr 4489, 2), (Sum.inr 4490, 1), (Sum.inr 4491, 1), (Sum.inr 4503, 2), (Sum.inr 4507, 1), (Sum.inr 4510, 1), (Sum.inr 5105, 2), (Sum.inr 5294, 1), (Sum.inr 5304, 1), (Sum.inr 5310, 1)]

theorem sourceEq1771 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1771 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1771 + difference 0 1) (sourceB1771 + difference 1 0) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA1771 + difference 0 1) (sourceB1771 + difference 1 0) sourceC1771) = raw8018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw8018; decide +kernel
    rw [ha]
    exact (canonical8018 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1771 + difference 0 2) (sourceB1771 + difference 2 0) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA1771 + difference 0 2) (sourceB1771 + difference 2 0) sourceC1771) = raw8019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw8019; decide +kernel
    rw [ha]
    exact (canonical8019 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1771 + difference 0 3) (sourceB1771 + difference 3 0) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1771 + difference 0 3) (sourceB1771 + difference 3 0) sourceC1771) = raw13990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw13990; decide +kernel
    rw [ha]
    exact (canonical13990 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1771 + difference 0 4) (sourceB1771 + difference 4 0) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA1771 + difference 0 4) (sourceB1771 + difference 4 0) sourceC1771) = raw8020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw8020; decide +kernel
    rw [ha]
    exact (canonical8020 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1771 + difference 0 5) (sourceB1771 + difference 5 0) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA1771 + difference 0 5) (sourceB1771 + difference 5 0) sourceC1771) = raw8021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw8021; decide +kernel
    rw [ha]
    exact (canonical8021 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1771 + difference 1 0) (sourceB1771 + difference 0 1) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4126) := by
    have ha : (tripleCharges (sourceA1771 + difference 1 0) (sourceB1771 + difference 0 1) sourceC1771) = raw25663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25663; decide +kernel
    rw [ha]
    exact (canonical25663 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1771 + difference 1 2) (sourceB1771 + difference 2 1) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4307) := by
    have ha : (tripleCharges (sourceA1771 + difference 1 2) (sourceB1771 + difference 2 1) sourceC1771) = raw25664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25664; decide +kernel
    rw [ha]
    exact (canonical25664 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1771 + difference 1 3) (sourceB1771 + difference 3 1) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1771 + difference 1 3) (sourceB1771 + difference 3 1) sourceC1771) = raw8007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw8007; decide +kernel
    rw [ha]
    exact (canonical8007 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1771 + difference 1 4) (sourceB1771 + difference 4 1) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1771 + difference 1 4) (sourceB1771 + difference 4 1) sourceC1771) = raw25665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25665; decide +kernel
    rw [ha]
    exact (canonical25665 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1771 + difference 1 5) (sourceB1771 + difference 5 1) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1771 + difference 1 5) (sourceB1771 + difference 5 1) sourceC1771) = raw13973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw13973; decide +kernel
    rw [ha]
    exact (canonical13973 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1771 + difference 2 0) (sourceB1771 + difference 0 2) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4126) := by
    have ha : (tripleCharges (sourceA1771 + difference 2 0) (sourceB1771 + difference 0 2) sourceC1771) = raw25666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25666; decide +kernel
    rw [ha]
    exact (canonical25666 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1771 + difference 2 1) (sourceB1771 + difference 1 2) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4307) := by
    have ha : (tripleCharges (sourceA1771 + difference 2 1) (sourceB1771 + difference 1 2) sourceC1771) = raw25667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25667; decide +kernel
    rw [ha]
    exact (canonical25667 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1771 + difference 2 3) (sourceB1771 + difference 3 2) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1771 + difference 2 3) (sourceB1771 + difference 3 2) sourceC1771) = raw8012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw8012; decide +kernel
    rw [ha]
    exact (canonical8012 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1771 + difference 2 4) (sourceB1771 + difference 4 2) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1771 + difference 2 4) (sourceB1771 + difference 4 2) sourceC1771) = raw25668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25668; decide +kernel
    rw [ha]
    exact (canonical25668 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1771 + difference 2 5) (sourceB1771 + difference 5 2) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1771 + difference 2 5) (sourceB1771 + difference 5 2) sourceC1771) = raw13977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw13977; decide +kernel
    rw [ha]
    exact (canonical13977 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1771 + difference 3 0) (sourceB1771 + difference 0 3) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4129) := by
    have ha : (tripleCharges (sourceA1771 + difference 3 0) (sourceB1771 + difference 0 3) sourceC1771) = raw25669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25669; decide +kernel
    rw [ha]
    exact (canonical25669 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1771 + difference 3 1) (sourceB1771 + difference 1 3) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA1771 + difference 3 1) (sourceB1771 + difference 1 3) sourceC1771) = raw25670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25670; decide +kernel
    rw [ha]
    exact (canonical25670 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1771 + difference 3 2) (sourceB1771 + difference 2 3) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA1771 + difference 3 2) (sourceB1771 + difference 2 3) sourceC1771) = raw25671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25671; decide +kernel
    rw [ha]
    exact (canonical25671 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1771 + difference 3 4) (sourceB1771 + difference 4 3) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1771 + difference 3 4) (sourceB1771 + difference 4 3) sourceC1771) = raw25672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25672; decide +kernel
    rw [ha]
    exact (canonical25672 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1771 + difference 3 5) (sourceB1771 + difference 5 3) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1771 + difference 3 5) (sourceB1771 + difference 5 3) sourceC1771) = raw13981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw13981; decide +kernel
    rw [ha]
    exact (canonical13981 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1771 + difference 4 0) (sourceB1771 + difference 0 4) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4132) := by
    have ha : (tripleCharges (sourceA1771 + difference 4 0) (sourceB1771 + difference 0 4) sourceC1771) = raw25673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25673; decide +kernel
    rw [ha]
    exact (canonical25673 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1771 + difference 4 1) (sourceB1771 + difference 1 4) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4313) := by
    have ha : (tripleCharges (sourceA1771 + difference 4 1) (sourceB1771 + difference 1 4) sourceC1771) = raw25674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25674; decide +kernel
    rw [ha]
    exact (canonical25674 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1771 + difference 4 2) (sourceB1771 + difference 2 4) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4313) := by
    have ha : (tripleCharges (sourceA1771 + difference 4 2) (sourceB1771 + difference 2 4) sourceC1771) = raw25675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25675; decide +kernel
    rw [ha]
    exact (canonical25675 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1771 + difference 4 3) (sourceB1771 + difference 3 4) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1771 + difference 4 3) (sourceB1771 + difference 3 4) sourceC1771) = raw8022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw8022; decide +kernel
    rw [ha]
    exact (canonical8022 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1771 + difference 4 5) (sourceB1771 + difference 5 4) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA1771 + difference 4 5) (sourceB1771 + difference 5 4) sourceC1771) = raw13986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw13986; decide +kernel
    rw [ha]
    exact (canonical13986 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1771 + difference 5 0) (sourceB1771 + difference 0 5) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4128) := by
    have ha : (tripleCharges (sourceA1771 + difference 5 0) (sourceB1771 + difference 0 5) sourceC1771) = raw25676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25676; decide +kernel
    rw [ha]
    exact (canonical25676 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1771 + difference 5 1) (sourceB1771 + difference 1 5) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1771 + difference 5 1) (sourceB1771 + difference 1 5) sourceC1771) = raw25677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25677; decide +kernel
    rw [ha]
    exact (canonical25677 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1771 + difference 5 2) (sourceB1771 + difference 2 5) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1771 + difference 5 2) (sourceB1771 + difference 2 5) sourceC1771) = raw25678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25678; decide +kernel
    rw [ha]
    exact (canonical25678 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1771 + difference 5 3) (sourceB1771 + difference 3 5) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1771 + difference 5 3) (sourceB1771 + difference 3 5) sourceC1771) = raw8027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw8027; decide +kernel
    rw [ha]
    exact (canonical8027 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1771 + difference 5 4) (sourceB1771 + difference 4 5) sourceC1771) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1771 + difference 5 4) (sourceB1771 + difference 4 5) sourceC1771) = raw25679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1771 sourceB1771 sourceC1771 difference raw25679; decide +kernel
    rw [ha]
    exact (canonical25679 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1771 sourceB1771 sourceC1771
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1771, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1772 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1772 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1772 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceForm1772 : Integer.Sparse Master := [(Sum.inr 557, 2), (Sum.inr 559, 1), (Sum.inr 560, 1), (Sum.inr 562, 1), (Sum.inr 885, 2), (Sum.inr 887, 2), (Sum.inr 888, 2), (Sum.inr 891, 2), (Sum.inr 1044, 2), (Sum.inr 1046, 1), (Sum.inr 1049, 1), (Sum.inr 1073, 2), (Sum.inr 1074, 1), (Sum.inr 1075, 1), (Sum.inr 1087, 2), (Sum.inr 1091, 1), (Sum.inr 1094, 1), (Sum.inr 2515, 2), (Sum.inr 2768, 1), (Sum.inr 2782, 1), (Sum.inr 2788, 1)]

theorem sourceEq1772 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1772 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1772 + difference 0 1) (sourceB1772 + difference 1 0) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA1772 + difference 0 1) (sourceB1772 + difference 1 0) sourceC1772) = raw8048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw8048; decide +kernel
    rw [ha]
    exact (canonical8048 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1772 + difference 0 2) (sourceB1772 + difference 2 0) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA1772 + difference 0 2) (sourceB1772 + difference 2 0) sourceC1772) = raw8049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw8049; decide +kernel
    rw [ha]
    exact (canonical8049 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1772 + difference 0 3) (sourceB1772 + difference 3 0) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA1772 + difference 0 3) (sourceB1772 + difference 3 0) sourceC1772) = raw14012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw14012; decide +kernel
    rw [ha]
    exact (canonical14012 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1772 + difference 0 4) (sourceB1772 + difference 4 0) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA1772 + difference 0 4) (sourceB1772 + difference 4 0) sourceC1772) = raw8050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw8050; decide +kernel
    rw [ha]
    exact (canonical8050 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1772 + difference 0 5) (sourceB1772 + difference 5 0) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA1772 + difference 0 5) (sourceB1772 + difference 5 0) sourceC1772) = raw8051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw8051; decide +kernel
    rw [ha]
    exact (canonical8051 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1772 + difference 1 0) (sourceB1772 + difference 0 1) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 557) := by
    have ha : (tripleCharges (sourceA1772 + difference 1 0) (sourceB1772 + difference 0 1) sourceC1772) = raw25680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25680; decide +kernel
    rw [ha]
    exact (canonical25680 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1772 + difference 1 2) (sourceB1772 + difference 2 1) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 885) := by
    have ha : (tripleCharges (sourceA1772 + difference 1 2) (sourceB1772 + difference 2 1) sourceC1772) = raw25681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25681; decide +kernel
    rw [ha]
    exact (canonical25681 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1772 + difference 1 3) (sourceB1772 + difference 3 1) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1772 + difference 1 3) (sourceB1772 + difference 3 1) sourceC1772) = raw8037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw8037; decide +kernel
    rw [ha]
    exact (canonical8037 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1772 + difference 1 4) (sourceB1772 + difference 4 1) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1772 + difference 1 4) (sourceB1772 + difference 4 1) sourceC1772) = raw25682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25682; decide +kernel
    rw [ha]
    exact (canonical25682 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1772 + difference 1 5) (sourceB1772 + difference 5 1) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1772 + difference 1 5) (sourceB1772 + difference 5 1) sourceC1772) = raw13995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw13995; decide +kernel
    rw [ha]
    exact (canonical13995 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1772 + difference 2 0) (sourceB1772 + difference 0 2) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 557) := by
    have ha : (tripleCharges (sourceA1772 + difference 2 0) (sourceB1772 + difference 0 2) sourceC1772) = raw25683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25683; decide +kernel
    rw [ha]
    exact (canonical25683 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1772 + difference 2 1) (sourceB1772 + difference 1 2) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 885) := by
    have ha : (tripleCharges (sourceA1772 + difference 2 1) (sourceB1772 + difference 1 2) sourceC1772) = raw25684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25684; decide +kernel
    rw [ha]
    exact (canonical25684 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1772 + difference 2 3) (sourceB1772 + difference 3 2) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1772 + difference 2 3) (sourceB1772 + difference 3 2) sourceC1772) = raw8042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw8042; decide +kernel
    rw [ha]
    exact (canonical8042 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1772 + difference 2 4) (sourceB1772 + difference 4 2) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1772 + difference 2 4) (sourceB1772 + difference 4 2) sourceC1772) = raw25685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25685; decide +kernel
    rw [ha]
    exact (canonical25685 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1772 + difference 2 5) (sourceB1772 + difference 5 2) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1772 + difference 2 5) (sourceB1772 + difference 5 2) sourceC1772) = raw13999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw13999; decide +kernel
    rw [ha]
    exact (canonical13999 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1772 + difference 3 0) (sourceB1772 + difference 0 3) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 560) := by
    have ha : (tripleCharges (sourceA1772 + difference 3 0) (sourceB1772 + difference 0 3) sourceC1772) = raw25686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25686; decide +kernel
    rw [ha]
    exact (canonical25686 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1772 + difference 3 1) (sourceB1772 + difference 1 3) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA1772 + difference 3 1) (sourceB1772 + difference 1 3) sourceC1772) = raw25687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25687; decide +kernel
    rw [ha]
    exact (canonical25687 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1772 + difference 3 2) (sourceB1772 + difference 2 3) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA1772 + difference 3 2) (sourceB1772 + difference 2 3) sourceC1772) = raw25688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25688; decide +kernel
    rw [ha]
    exact (canonical25688 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1772 + difference 3 4) (sourceB1772 + difference 4 3) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA1772 + difference 3 4) (sourceB1772 + difference 4 3) sourceC1772) = raw25689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25689; decide +kernel
    rw [ha]
    exact (canonical25689 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1772 + difference 3 5) (sourceB1772 + difference 5 3) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1772 + difference 3 5) (sourceB1772 + difference 5 3) sourceC1772) = raw14003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw14003; decide +kernel
    rw [ha]
    exact (canonical14003 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1772 + difference 4 0) (sourceB1772 + difference 0 4) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 562) := by
    have ha : (tripleCharges (sourceA1772 + difference 4 0) (sourceB1772 + difference 0 4) sourceC1772) = raw25690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25690; decide +kernel
    rw [ha]
    exact (canonical25690 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1772 + difference 4 1) (sourceB1772 + difference 1 4) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 891) := by
    have ha : (tripleCharges (sourceA1772 + difference 4 1) (sourceB1772 + difference 1 4) sourceC1772) = raw25691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25691; decide +kernel
    rw [ha]
    exact (canonical25691 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1772 + difference 4 2) (sourceB1772 + difference 2 4) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 891) := by
    have ha : (tripleCharges (sourceA1772 + difference 4 2) (sourceB1772 + difference 2 4) sourceC1772) = raw25692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25692; decide +kernel
    rw [ha]
    exact (canonical25692 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1772 + difference 4 3) (sourceB1772 + difference 3 4) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1772 + difference 4 3) (sourceB1772 + difference 3 4) sourceC1772) = raw8052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw8052; decide +kernel
    rw [ha]
    exact (canonical8052 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1772 + difference 4 5) (sourceB1772 + difference 5 4) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1772 + difference 4 5) (sourceB1772 + difference 5 4) sourceC1772) = raw14008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw14008; decide +kernel
    rw [ha]
    exact (canonical14008 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1772 + difference 5 0) (sourceB1772 + difference 0 5) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 559) := by
    have ha : (tripleCharges (sourceA1772 + difference 5 0) (sourceB1772 + difference 0 5) sourceC1772) = raw25693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25693; decide +kernel
    rw [ha]
    exact (canonical25693 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1772 + difference 5 1) (sourceB1772 + difference 1 5) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1772 + difference 5 1) (sourceB1772 + difference 1 5) sourceC1772) = raw25694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25694; decide +kernel
    rw [ha]
    exact (canonical25694 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1772 + difference 5 2) (sourceB1772 + difference 2 5) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1772 + difference 5 2) (sourceB1772 + difference 2 5) sourceC1772) = raw25695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25695; decide +kernel
    rw [ha]
    exact (canonical25695 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1772 + difference 5 3) (sourceB1772 + difference 3 5) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1772 + difference 5 3) (sourceB1772 + difference 3 5) sourceC1772) = raw8057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw8057; decide +kernel
    rw [ha]
    exact (canonical8057 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1772 + difference 5 4) (sourceB1772 + difference 4 5) sourceC1772) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1772 + difference 5 4) (sourceB1772 + difference 4 5) sourceC1772) = raw25696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1772 sourceB1772 sourceC1772 difference raw25696; decide +kernel
    rw [ha]
    exact (canonical25696 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1772 sourceB1772 sourceC1772
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1772, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1773 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB1773 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1773 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1773 : Integer.Sparse Master := [(Sum.inr 4268, 2), (Sum.inr 4276, 1), (Sum.inr 4279, 1), (Sum.inr 4283, 1), (Sum.inr 4400, 2), (Sum.inr 4424, 2), (Sum.inr 4425, 2), (Sum.inr 4427, 2), (Sum.inr 4459, 2), (Sum.inr 4461, 2), (Sum.inr 4462, 2), (Sum.inr 4499, 1), (Sum.inr 4500, 1), (Sum.inr 4502, 1), (Sum.inr 4503, 1), (Sum.inr 4504, 1), (Sum.inr 4506, 1), (Sum.inr 4607, 2), (Sum.inr 4617, 1), (Sum.inr 4619, 1), (Sum.inr 4623, 1)]

theorem sourceEq1773 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1773 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1773 + difference 0 1) (sourceB1773 + difference 1 0) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1773 + difference 0 1) (sourceB1773 + difference 1 0) sourceC1773) = raw25697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25697; decide +kernel
    rw [ha]
    exact (canonical25697 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1773 + difference 0 2) (sourceB1773 + difference 2 0) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1773 + difference 0 2) (sourceB1773 + difference 2 0) sourceC1773) = raw24613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw24613; decide +kernel
    rw [ha]
    exact (canonical24613 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1773 + difference 0 3) (sourceB1773 + difference 3 0) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1773 + difference 0 3) (sourceB1773 + difference 3 0) sourceC1773) = raw24263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw24263; decide +kernel
    rw [ha]
    exact (canonical24263 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1773 + difference 0 4) (sourceB1773 + difference 4 0) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1773 + difference 0 4) (sourceB1773 + difference 4 0) sourceC1773) = raw25698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25698; decide +kernel
    rw [ha]
    exact (canonical25698 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1773 + difference 0 5) (sourceB1773 + difference 5 0) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1773 + difference 0 5) (sourceB1773 + difference 5 0) sourceC1773) = raw25699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25699; decide +kernel
    rw [ha]
    exact (canonical25699 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1773 + difference 1 0) (sourceB1773 + difference 0 1) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1773 + difference 1 0) (sourceB1773 + difference 0 1) sourceC1773) = raw25099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25099; decide +kernel
    rw [ha]
    exact (canonical25099 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1773 + difference 1 2) (sourceB1773 + difference 2 1) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4400) := by
    have ha : (tripleCharges (sourceA1773 + difference 1 2) (sourceB1773 + difference 2 1) sourceC1773) = raw25101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25101; decide +kernel
    rw [ha]
    exact (canonical25101 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1773 + difference 1 3) (sourceB1773 + difference 3 1) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1773 + difference 1 3) (sourceB1773 + difference 3 1) sourceC1773) = raw25285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25285; decide +kernel
    rw [ha]
    exact (canonical25285 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1773 + difference 1 4) (sourceB1773 + difference 4 1) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1773 + difference 1 4) (sourceB1773 + difference 4 1) sourceC1773) = raw25102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25102; decide +kernel
    rw [ha]
    exact (canonical25102 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1773 + difference 1 5) (sourceB1773 + difference 5 1) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA1773 + difference 1 5) (sourceB1773 + difference 5 1) sourceC1773) = raw25103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25103; decide +kernel
    rw [ha]
    exact (canonical25103 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1773 + difference 2 0) (sourceB1773 + difference 0 2) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1773 + difference 2 0) (sourceB1773 + difference 0 2) sourceC1773) = raw25700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25700; decide +kernel
    rw [ha]
    exact (canonical25700 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1773 + difference 2 1) (sourceB1773 + difference 1 2) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4400) := by
    have ha : (tripleCharges (sourceA1773 + difference 2 1) (sourceB1773 + difference 1 2) sourceC1773) = raw25701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25701; decide +kernel
    rw [ha]
    exact (canonical25701 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1773 + difference 2 3) (sourceB1773 + difference 3 2) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1773 + difference 2 3) (sourceB1773 + difference 3 2) sourceC1773) = raw25095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25095; decide +kernel
    rw [ha]
    exact (canonical25095 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1773 + difference 2 4) (sourceB1773 + difference 4 2) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1773 + difference 2 4) (sourceB1773 + difference 4 2) sourceC1773) = raw25702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25702; decide +kernel
    rw [ha]
    exact (canonical25702 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1773 + difference 2 5) (sourceB1773 + difference 5 2) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA1773 + difference 2 5) (sourceB1773 + difference 5 2) sourceC1773) = raw25703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25703; decide +kernel
    rw [ha]
    exact (canonical25703 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1773 + difference 3 0) (sourceB1773 + difference 0 3) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA1773 + difference 3 0) (sourceB1773 + difference 0 3) sourceC1773) = raw25704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25704; decide +kernel
    rw [ha]
    exact (canonical25704 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1773 + difference 3 1) (sourceB1773 + difference 1 3) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4425) := by
    have ha : (tripleCharges (sourceA1773 + difference 3 1) (sourceB1773 + difference 1 3) sourceC1773) = raw25705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25705; decide +kernel
    rw [ha]
    exact (canonical25705 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1773 + difference 3 2) (sourceB1773 + difference 2 3) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4425) := by
    have ha : (tripleCharges (sourceA1773 + difference 3 2) (sourceB1773 + difference 2 3) sourceC1773) = raw25706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25706; decide +kernel
    rw [ha]
    exact (canonical25706 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1773 + difference 3 4) (sourceB1773 + difference 4 3) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA1773 + difference 3 4) (sourceB1773 + difference 4 3) sourceC1773) = raw25707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25707; decide +kernel
    rw [ha]
    exact (canonical25707 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1773 + difference 3 5) (sourceB1773 + difference 5 3) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4504) := by
    have ha : (tripleCharges (sourceA1773 + difference 3 5) (sourceB1773 + difference 5 3) sourceC1773) = raw25708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25708; decide +kernel
    rw [ha]
    exact (canonical25708 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1773 + difference 4 0) (sourceB1773 + difference 0 4) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4279) := by
    have ha : (tripleCharges (sourceA1773 + difference 4 0) (sourceB1773 + difference 0 4) sourceC1773) = raw25709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25709; decide +kernel
    rw [ha]
    exact (canonical25709 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1773 + difference 4 1) (sourceB1773 + difference 1 4) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4427) := by
    have ha : (tripleCharges (sourceA1773 + difference 4 1) (sourceB1773 + difference 1 4) sourceC1773) = raw25710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25710; decide +kernel
    rw [ha]
    exact (canonical25710 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1773 + difference 4 2) (sourceB1773 + difference 2 4) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4427) := by
    have ha : (tripleCharges (sourceA1773 + difference 4 2) (sourceB1773 + difference 2 4) sourceC1773) = raw25711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25711; decide +kernel
    rw [ha]
    exact (canonical25711 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1773 + difference 4 3) (sourceB1773 + difference 3 4) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1773 + difference 4 3) (sourceB1773 + difference 3 4) sourceC1773) = raw24413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw24413; decide +kernel
    rw [ha]
    exact (canonical24413 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1773 + difference 4 5) (sourceB1773 + difference 5 4) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4506) := by
    have ha : (tripleCharges (sourceA1773 + difference 4 5) (sourceB1773 + difference 5 4) sourceC1773) = raw25712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25712; decide +kernel
    rw [ha]
    exact (canonical25712 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1773 + difference 5 0) (sourceB1773 + difference 0 5) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4283) := by
    have ha : (tripleCharges (sourceA1773 + difference 5 0) (sourceB1773 + difference 0 5) sourceC1773) = raw25713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25713; decide +kernel
    rw [ha]
    exact (canonical25713 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1773 + difference 5 1) (sourceB1773 + difference 1 5) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1773 + difference 5 1) (sourceB1773 + difference 1 5) sourceC1773) = raw25714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25714; decide +kernel
    rw [ha]
    exact (canonical25714 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1773 + difference 5 2) (sourceB1773 + difference 2 5) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1773 + difference 5 2) (sourceB1773 + difference 2 5) sourceC1773) = raw24609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw24609; decide +kernel
    rw [ha]
    exact (canonical24609 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1773 + difference 5 3) (sourceB1773 + difference 3 5) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1773 + difference 5 3) (sourceB1773 + difference 3 5) sourceC1773) = raw24260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw24260; decide +kernel
    rw [ha]
    exact (canonical24260 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1773 + difference 5 4) (sourceB1773 + difference 4 5) sourceC1773) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1773 + difference 5 4) (sourceB1773 + difference 4 5) sourceC1773) = raw25282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1773 sourceB1773 sourceC1773 difference raw25282; decide +kernel
    rw [ha]
    exact (canonical25282 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1773 sourceB1773 sourceC1773
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1773, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1774 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB1774 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1774 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1774 : Integer.Sparse Master := [(Sum.inr 811, 2), (Sum.inr 856, 1), (Sum.inr 857, 1), (Sum.inr 858, 1), (Sum.inr 981, 2), (Sum.inr 1005, 2), (Sum.inr 1006, 2), (Sum.inr 1008, 2), (Sum.inr 1042, 2), (Sum.inr 1044, 2), (Sum.inr 1045, 2), (Sum.inr 1083, 1), (Sum.inr 1084, 1), (Sum.inr 1086, 1), (Sum.inr 1087, 1), (Sum.inr 1088, 1), (Sum.inr 1090, 1), (Sum.inr 1241, 2), (Sum.inr 1302, 1), (Sum.inr 1305, 1), (Sum.inr 1306, 1)]

theorem sourceEq1774 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1774 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1774 + difference 0 1) (sourceB1774 + difference 1 0) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1774 + difference 0 1) (sourceB1774 + difference 1 0) sourceC1774) = raw25715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25715; decide +kernel
    rw [ha]
    exact (canonical25715 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1774 + difference 0 2) (sourceB1774 + difference 2 0) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1774 + difference 0 2) (sourceB1774 + difference 2 0) sourceC1774) = raw24639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw24639; decide +kernel
    rw [ha]
    exact (canonical24639 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1774 + difference 0 3) (sourceB1774 + difference 3 0) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1774 + difference 0 3) (sourceB1774 + difference 3 0) sourceC1774) = raw24634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw24634; decide +kernel
    rw [ha]
    exact (canonical24634 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1774 + difference 0 4) (sourceB1774 + difference 4 0) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1302) := by
    have ha : (tripleCharges (sourceA1774 + difference 0 4) (sourceB1774 + difference 4 0) sourceC1774) = raw25716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25716; decide +kernel
    rw [ha]
    exact (canonical25716 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1774 + difference 0 5) (sourceB1774 + difference 5 0) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1774 + difference 0 5) (sourceB1774 + difference 5 0) sourceC1774) = raw25717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25717; decide +kernel
    rw [ha]
    exact (canonical25717 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1774 + difference 1 0) (sourceB1774 + difference 0 1) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1774 + difference 1 0) (sourceB1774 + difference 0 1) sourceC1774) = raw25122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25122; decide +kernel
    rw [ha]
    exact (canonical25122 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1774 + difference 1 2) (sourceB1774 + difference 2 1) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 981) := by
    have ha : (tripleCharges (sourceA1774 + difference 1 2) (sourceB1774 + difference 2 1) sourceC1774) = raw25124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25124; decide +kernel
    rw [ha]
    exact (canonical25124 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1774 + difference 1 3) (sourceB1774 + difference 3 1) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1774 + difference 1 3) (sourceB1774 + difference 3 1) sourceC1774) = raw25302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25302; decide +kernel
    rw [ha]
    exact (canonical25302 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1774 + difference 1 4) (sourceB1774 + difference 4 1) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA1774 + difference 1 4) (sourceB1774 + difference 4 1) sourceC1774) = raw25125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25125; decide +kernel
    rw [ha]
    exact (canonical25125 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1774 + difference 1 5) (sourceB1774 + difference 5 1) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA1774 + difference 1 5) (sourceB1774 + difference 5 1) sourceC1774) = raw25126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25126; decide +kernel
    rw [ha]
    exact (canonical25126 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1774 + difference 2 0) (sourceB1774 + difference 0 2) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1774 + difference 2 0) (sourceB1774 + difference 0 2) sourceC1774) = raw25718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25718; decide +kernel
    rw [ha]
    exact (canonical25718 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1774 + difference 2 1) (sourceB1774 + difference 1 2) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 981) := by
    have ha : (tripleCharges (sourceA1774 + difference 2 1) (sourceB1774 + difference 1 2) sourceC1774) = raw25719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25719; decide +kernel
    rw [ha]
    exact (canonical25719 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1774 + difference 2 3) (sourceB1774 + difference 3 2) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1774 + difference 2 3) (sourceB1774 + difference 3 2) sourceC1774) = raw25118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25118; decide +kernel
    rw [ha]
    exact (canonical25118 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1774 + difference 2 4) (sourceB1774 + difference 4 2) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA1774 + difference 2 4) (sourceB1774 + difference 4 2) sourceC1774) = raw25720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25720; decide +kernel
    rw [ha]
    exact (canonical25720 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1774 + difference 2 5) (sourceB1774 + difference 5 2) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA1774 + difference 2 5) (sourceB1774 + difference 5 2) sourceC1774) = raw25721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25721; decide +kernel
    rw [ha]
    exact (canonical25721 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1774 + difference 3 0) (sourceB1774 + difference 0 3) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 857) := by
    have ha : (tripleCharges (sourceA1774 + difference 3 0) (sourceB1774 + difference 0 3) sourceC1774) = raw25722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25722; decide +kernel
    rw [ha]
    exact (canonical25722 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1774 + difference 3 1) (sourceB1774 + difference 1 3) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1006) := by
    have ha : (tripleCharges (sourceA1774 + difference 3 1) (sourceB1774 + difference 1 3) sourceC1774) = raw25723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25723; decide +kernel
    rw [ha]
    exact (canonical25723 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1774 + difference 3 2) (sourceB1774 + difference 2 3) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1006) := by
    have ha : (tripleCharges (sourceA1774 + difference 3 2) (sourceB1774 + difference 2 3) sourceC1774) = raw25724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25724; decide +kernel
    rw [ha]
    exact (canonical25724 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1774 + difference 3 4) (sourceB1774 + difference 4 3) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1084) := by
    have ha : (tripleCharges (sourceA1774 + difference 3 4) (sourceB1774 + difference 4 3) sourceC1774) = raw25725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25725; decide +kernel
    rw [ha]
    exact (canonical25725 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1774 + difference 3 5) (sourceB1774 + difference 5 3) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1088) := by
    have ha : (tripleCharges (sourceA1774 + difference 3 5) (sourceB1774 + difference 5 3) sourceC1774) = raw25726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25726; decide +kernel
    rw [ha]
    exact (canonical25726 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1774 + difference 4 0) (sourceB1774 + difference 0 4) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 858) := by
    have ha : (tripleCharges (sourceA1774 + difference 4 0) (sourceB1774 + difference 0 4) sourceC1774) = raw25727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25727; decide +kernel
    rw [ha]
    exact (canonical25727 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1774 + difference 4 1) (sourceB1774 + difference 1 4) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1008) := by
    have ha : (tripleCharges (sourceA1774 + difference 4 1) (sourceB1774 + difference 1 4) sourceC1774) = raw25728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25728; decide +kernel
    rw [ha]
    exact (canonical25728 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1774 + difference 4 2) (sourceB1774 + difference 2 4) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1008) := by
    have ha : (tripleCharges (sourceA1774 + difference 4 2) (sourceB1774 + difference 2 4) sourceC1774) = raw25729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25729; decide +kernel
    rw [ha]
    exact (canonical25729 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1774 + difference 4 3) (sourceB1774 + difference 3 4) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1774 + difference 4 3) (sourceB1774 + difference 3 4) sourceC1774) = raw25128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25128; decide +kernel
    rw [ha]
    exact (canonical25128 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1774 + difference 4 5) (sourceB1774 + difference 5 4) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1090) := by
    have ha : (tripleCharges (sourceA1774 + difference 4 5) (sourceB1774 + difference 5 4) sourceC1774) = raw25730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25730; decide +kernel
    rw [ha]
    exact (canonical25730 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1774 + difference 5 0) (sourceB1774 + difference 0 5) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 856) := by
    have ha : (tripleCharges (sourceA1774 + difference 5 0) (sourceB1774 + difference 0 5) sourceC1774) = raw25731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25731; decide +kernel
    rw [ha]
    exact (canonical25731 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1774 + difference 5 1) (sourceB1774 + difference 1 5) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1774 + difference 5 1) (sourceB1774 + difference 1 5) sourceC1774) = raw25732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25732; decide +kernel
    rw [ha]
    exact (canonical25732 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1774 + difference 5 2) (sourceB1774 + difference 2 5) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1774 + difference 5 2) (sourceB1774 + difference 2 5) sourceC1774) = raw24635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw24635; decide +kernel
    rw [ha]
    exact (canonical24635 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1774 + difference 5 3) (sourceB1774 + difference 3 5) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1774 + difference 5 3) (sourceB1774 + difference 3 5) sourceC1774) = raw24630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw24630; decide +kernel
    rw [ha]
    exact (canonical24630 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1774 + difference 5 4) (sourceB1774 + difference 4 5) sourceC1774) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1774 + difference 5 4) (sourceB1774 + difference 4 5) sourceC1774) = raw25299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1774 sourceB1774 sourceC1774 difference raw25299; decide +kernel
    rw [ha]
    exact (canonical25299 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1774 sourceB1774 sourceC1774
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1774, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1775 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1775 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1775 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceForm1775 : Integer.Sparse Master := [(Sum.inr 4173, 2), (Sum.inr 4178, 1), (Sum.inr 4180, 1), (Sum.inr 4188, 1), (Sum.inr 4342, 2), (Sum.inr 4347, 2), (Sum.inr 4349, 2), (Sum.inr 4357, 2), (Sum.inr 4474, 2), (Sum.inr 4476, 1), (Sum.inr 4480, 1), (Sum.inr 4495, 2), (Sum.inr 4498, 1), (Sum.inr 4499, 2), (Sum.inr 4503, 1), (Sum.inr 4507, 1), (Sum.inr 4511, 1), (Sum.inr 4835, 2), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4901, 1)]

theorem sourceEq1775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1775 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1775 + difference 0 1) (sourceB1775 + difference 1 0) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA1775 + difference 0 1) (sourceB1775 + difference 1 0) sourceC1775) = raw25733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25733; decide +kernel
    rw [ha]
    exact (canonical25733 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1775 + difference 0 2) (sourceB1775 + difference 2 0) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA1775 + difference 0 2) (sourceB1775 + difference 2 0) sourceC1775) = raw25734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25734; decide +kernel
    rw [ha]
    exact (canonical25734 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1775 + difference 0 3) (sourceB1775 + difference 3 0) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA1775 + difference 0 3) (sourceB1775 + difference 3 0) sourceC1775) = raw25735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25735; decide +kernel
    rw [ha]
    exact (canonical25735 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1775 + difference 0 4) (sourceB1775 + difference 4 0) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA1775 + difference 0 4) (sourceB1775 + difference 4 0) sourceC1775) = raw25736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25736; decide +kernel
    rw [ha]
    exact (canonical25736 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1775 + difference 0 5) (sourceB1775 + difference 5 0) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1775 + difference 0 5) (sourceB1775 + difference 5 0) sourceC1775) = raw25737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25737; decide +kernel
    rw [ha]
    exact (canonical25737 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1775 + difference 1 0) (sourceB1775 + difference 0 1) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1775 + difference 1 0) (sourceB1775 + difference 0 1) sourceC1775) = raw25738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25738; decide +kernel
    rw [ha]
    exact (canonical25738 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1775 + difference 1 2) (sourceB1775 + difference 2 1) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4342) := by
    have ha : (tripleCharges (sourceA1775 + difference 1 2) (sourceB1775 + difference 2 1) sourceC1775) = raw25739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25739; decide +kernel
    rw [ha]
    exact (canonical25739 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1775 + difference 1 3) (sourceB1775 + difference 3 1) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA1775 + difference 1 3) (sourceB1775 + difference 3 1) sourceC1775) = raw25740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25740; decide +kernel
    rw [ha]
    exact (canonical25740 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1775 + difference 1 4) (sourceB1775 + difference 4 1) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1775 + difference 1 4) (sourceB1775 + difference 4 1) sourceC1775) = raw25741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25741; decide +kernel
    rw [ha]
    exact (canonical25741 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1775 + difference 1 5) (sourceB1775 + difference 5 1) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1775 + difference 1 5) (sourceB1775 + difference 5 1) sourceC1775) = raw25742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25742; decide +kernel
    rw [ha]
    exact (canonical25742 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1775 + difference 2 0) (sourceB1775 + difference 0 2) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1775 + difference 2 0) (sourceB1775 + difference 0 2) sourceC1775) = raw25743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25743; decide +kernel
    rw [ha]
    exact (canonical25743 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1775 + difference 2 1) (sourceB1775 + difference 1 2) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4342) := by
    have ha : (tripleCharges (sourceA1775 + difference 2 1) (sourceB1775 + difference 1 2) sourceC1775) = raw25744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25744; decide +kernel
    rw [ha]
    exact (canonical25744 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1775 + difference 2 3) (sourceB1775 + difference 3 2) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA1775 + difference 2 3) (sourceB1775 + difference 3 2) sourceC1775) = raw25745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25745; decide +kernel
    rw [ha]
    exact (canonical25745 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1775 + difference 2 4) (sourceB1775 + difference 4 2) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1775 + difference 2 4) (sourceB1775 + difference 4 2) sourceC1775) = raw25746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25746; decide +kernel
    rw [ha]
    exact (canonical25746 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1775 + difference 2 5) (sourceB1775 + difference 5 2) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1775 + difference 2 5) (sourceB1775 + difference 5 2) sourceC1775) = raw25747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25747; decide +kernel
    rw [ha]
    exact (canonical25747 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1775 + difference 3 0) (sourceB1775 + difference 0 3) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1775 + difference 3 0) (sourceB1775 + difference 0 3) sourceC1775) = raw25748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25748; decide +kernel
    rw [ha]
    exact (canonical25748 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1775 + difference 3 1) (sourceB1775 + difference 1 3) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1775 + difference 3 1) (sourceB1775 + difference 1 3) sourceC1775) = raw25749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25749; decide +kernel
    rw [ha]
    exact (canonical25749 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1775 + difference 3 2) (sourceB1775 + difference 2 3) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1775 + difference 3 2) (sourceB1775 + difference 2 3) sourceC1775) = raw25750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25750; decide +kernel
    rw [ha]
    exact (canonical25750 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1775 + difference 3 4) (sourceB1775 + difference 4 3) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1775 + difference 3 4) (sourceB1775 + difference 4 3) sourceC1775) = raw25751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25751; decide +kernel
    rw [ha]
    exact (canonical25751 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1775 + difference 3 5) (sourceB1775 + difference 5 3) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1775 + difference 3 5) (sourceB1775 + difference 5 3) sourceC1775) = raw25752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25752; decide +kernel
    rw [ha]
    exact (canonical25752 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1775 + difference 4 0) (sourceB1775 + difference 0 4) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4188) := by
    have ha : (tripleCharges (sourceA1775 + difference 4 0) (sourceB1775 + difference 0 4) sourceC1775) = raw25753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25753; decide +kernel
    rw [ha]
    exact (canonical25753 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1775 + difference 4 1) (sourceB1775 + difference 1 4) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA1775 + difference 4 1) (sourceB1775 + difference 1 4) sourceC1775) = raw25754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25754; decide +kernel
    rw [ha]
    exact (canonical25754 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1775 + difference 4 2) (sourceB1775 + difference 2 4) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA1775 + difference 4 2) (sourceB1775 + difference 2 4) sourceC1775) = raw25755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25755; decide +kernel
    rw [ha]
    exact (canonical25755 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1775 + difference 4 3) (sourceB1775 + difference 3 4) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA1775 + difference 4 3) (sourceB1775 + difference 3 4) sourceC1775) = raw25756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25756; decide +kernel
    rw [ha]
    exact (canonical25756 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1775 + difference 4 5) (sourceB1775 + difference 5 4) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1775 + difference 4 5) (sourceB1775 + difference 5 4) sourceC1775) = raw25757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25757; decide +kernel
    rw [ha]
    exact (canonical25757 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1775 + difference 5 0) (sourceB1775 + difference 0 5) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4178) := by
    have ha : (tripleCharges (sourceA1775 + difference 5 0) (sourceB1775 + difference 0 5) sourceC1775) = raw25758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25758; decide +kernel
    rw [ha]
    exact (canonical25758 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1775 + difference 5 1) (sourceB1775 + difference 1 5) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1775 + difference 5 1) (sourceB1775 + difference 1 5) sourceC1775) = raw25759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25759; decide +kernel
    rw [ha]
    exact (canonical25759 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1775 + difference 5 2) (sourceB1775 + difference 2 5) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1775 + difference 5 2) (sourceB1775 + difference 2 5) sourceC1775) = raw25760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25760; decide +kernel
    rw [ha]
    exact (canonical25760 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1775 + difference 5 3) (sourceB1775 + difference 3 5) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA1775 + difference 5 3) (sourceB1775 + difference 3 5) sourceC1775) = raw25761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25761; decide +kernel
    rw [ha]
    exact (canonical25761 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1775 + difference 5 4) (sourceB1775 + difference 4 5) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1775 + difference 5 4) (sourceB1775 + difference 4 5) sourceC1775) = raw25762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25762; decide +kernel
    rw [ha]
    exact (canonical25762 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1775 sourceB1775 sourceC1775
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1775, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1776 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1776 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1776 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceForm1776 : Integer.Sparse Master := [(Sum.inr 1508, 2), (Sum.inr 1519, 1), (Sum.inr 1520, 1), (Sum.inr 1526, 1), (Sum.inr 1665, 2), (Sum.inr 1675, 2), (Sum.inr 1676, 2), (Sum.inr 1682, 2), (Sum.inr 1708, 2), (Sum.inr 1709, 2), (Sum.inr 1727, 1), (Sum.inr 1728, 2), (Sum.inr 1729, 1), (Sum.inr 1739, 1), (Sum.inr 1740, 1), (Sum.inr 1755, 1), (Sum.inr 1756, 1), (Sum.inr 2206, 2), (Sum.inr 2265, 1), (Sum.inr 2266, 1), (Sum.inr 2293, 1)]

theorem sourceEq1776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1776 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1776 + difference 0 1) (sourceB1776 + difference 1 0) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1776 + difference 0 1) (sourceB1776 + difference 1 0) sourceC1776) = raw25763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25763; decide +kernel
    rw [ha]
    exact (canonical25763 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1776 + difference 0 2) (sourceB1776 + difference 2 0) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1776 + difference 0 2) (sourceB1776 + difference 2 0) sourceC1776) = raw25764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25764; decide +kernel
    rw [ha]
    exact (canonical25764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1776 + difference 0 3) (sourceB1776 + difference 3 0) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA1776 + difference 0 3) (sourceB1776 + difference 3 0) sourceC1776) = raw25765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25765; decide +kernel
    rw [ha]
    exact (canonical25765 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1776 + difference 0 4) (sourceB1776 + difference 4 0) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA1776 + difference 0 4) (sourceB1776 + difference 4 0) sourceC1776) = raw25766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25766; decide +kernel
    rw [ha]
    exact (canonical25766 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1776 + difference 0 5) (sourceB1776 + difference 5 0) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA1776 + difference 0 5) (sourceB1776 + difference 5 0) sourceC1776) = raw25767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25767; decide +kernel
    rw [ha]
    exact (canonical25767 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1776 + difference 1 0) (sourceB1776 + difference 0 1) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1776 + difference 1 0) (sourceB1776 + difference 0 1) sourceC1776) = raw25768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25768; decide +kernel
    rw [ha]
    exact (canonical25768 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1776 + difference 1 2) (sourceB1776 + difference 2 1) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1665) := by
    have ha : (tripleCharges (sourceA1776 + difference 1 2) (sourceB1776 + difference 2 1) sourceC1776) = raw25769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25769; decide +kernel
    rw [ha]
    exact (canonical25769 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1776 + difference 1 3) (sourceB1776 + difference 3 1) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1776 + difference 1 3) (sourceB1776 + difference 3 1) sourceC1776) = raw25770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25770; decide +kernel
    rw [ha]
    exact (canonical25770 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1776 + difference 1 4) (sourceB1776 + difference 4 1) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1776 + difference 1 4) (sourceB1776 + difference 4 1) sourceC1776) = raw25771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25771; decide +kernel
    rw [ha]
    exact (canonical25771 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1776 + difference 1 5) (sourceB1776 + difference 5 1) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1776 + difference 1 5) (sourceB1776 + difference 5 1) sourceC1776) = raw25772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25772; decide +kernel
    rw [ha]
    exact (canonical25772 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1776 + difference 2 0) (sourceB1776 + difference 0 2) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1776 + difference 2 0) (sourceB1776 + difference 0 2) sourceC1776) = raw25773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25773; decide +kernel
    rw [ha]
    exact (canonical25773 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1776 + difference 2 1) (sourceB1776 + difference 1 2) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1665) := by
    have ha : (tripleCharges (sourceA1776 + difference 2 1) (sourceB1776 + difference 1 2) sourceC1776) = raw25774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25774; decide +kernel
    rw [ha]
    exact (canonical25774 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1776 + difference 2 3) (sourceB1776 + difference 3 2) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1776 + difference 2 3) (sourceB1776 + difference 3 2) sourceC1776) = raw25775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25775; decide +kernel
    rw [ha]
    exact (canonical25775 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1776 + difference 2 4) (sourceB1776 + difference 4 2) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1776 + difference 2 4) (sourceB1776 + difference 4 2) sourceC1776) = raw25776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25776; decide +kernel
    rw [ha]
    exact (canonical25776 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1776 + difference 2 5) (sourceB1776 + difference 5 2) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1776 + difference 2 5) (sourceB1776 + difference 5 2) sourceC1776) = raw25777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25777; decide +kernel
    rw [ha]
    exact (canonical25777 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1776 + difference 3 0) (sourceB1776 + difference 0 3) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA1776 + difference 3 0) (sourceB1776 + difference 0 3) sourceC1776) = raw25778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25778; decide +kernel
    rw [ha]
    exact (canonical25778 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1776 + difference 3 1) (sourceB1776 + difference 1 3) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1776 + difference 3 1) (sourceB1776 + difference 1 3) sourceC1776) = raw25779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25779; decide +kernel
    rw [ha]
    exact (canonical25779 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1776 + difference 3 2) (sourceB1776 + difference 2 3) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1776 + difference 3 2) (sourceB1776 + difference 2 3) sourceC1776) = raw25780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25780; decide +kernel
    rw [ha]
    exact (canonical25780 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1776 + difference 3 4) (sourceB1776 + difference 4 3) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1776 + difference 3 4) (sourceB1776 + difference 4 3) sourceC1776) = raw25781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25781; decide +kernel
    rw [ha]
    exact (canonical25781 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1776 + difference 3 5) (sourceB1776 + difference 5 3) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1776 + difference 3 5) (sourceB1776 + difference 5 3) sourceC1776) = raw25782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25782; decide +kernel
    rw [ha]
    exact (canonical25782 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1776 + difference 4 0) (sourceB1776 + difference 0 4) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1526) := by
    have ha : (tripleCharges (sourceA1776 + difference 4 0) (sourceB1776 + difference 0 4) sourceC1776) = raw25783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25783; decide +kernel
    rw [ha]
    exact (canonical25783 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1776 + difference 4 1) (sourceB1776 + difference 1 4) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA1776 + difference 4 1) (sourceB1776 + difference 1 4) sourceC1776) = raw25784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25784; decide +kernel
    rw [ha]
    exact (canonical25784 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1776 + difference 4 2) (sourceB1776 + difference 2 4) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA1776 + difference 4 2) (sourceB1776 + difference 2 4) sourceC1776) = raw25785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25785; decide +kernel
    rw [ha]
    exact (canonical25785 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1776 + difference 4 3) (sourceB1776 + difference 3 4) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1776 + difference 4 3) (sourceB1776 + difference 3 4) sourceC1776) = raw25786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25786; decide +kernel
    rw [ha]
    exact (canonical25786 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1776 + difference 4 5) (sourceB1776 + difference 5 4) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1776 + difference 4 5) (sourceB1776 + difference 5 4) sourceC1776) = raw25787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25787; decide +kernel
    rw [ha]
    exact (canonical25787 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1776 + difference 5 0) (sourceB1776 + difference 0 5) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1776 + difference 5 0) (sourceB1776 + difference 0 5) sourceC1776) = raw25788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25788; decide +kernel
    rw [ha]
    exact (canonical25788 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1776 + difference 5 1) (sourceB1776 + difference 1 5) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1776 + difference 5 1) (sourceB1776 + difference 1 5) sourceC1776) = raw25789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25789; decide +kernel
    rw [ha]
    exact (canonical25789 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1776 + difference 5 2) (sourceB1776 + difference 2 5) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1776 + difference 5 2) (sourceB1776 + difference 2 5) sourceC1776) = raw25790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25790; decide +kernel
    rw [ha]
    exact (canonical25790 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1776 + difference 5 3) (sourceB1776 + difference 3 5) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1776 + difference 5 3) (sourceB1776 + difference 3 5) sourceC1776) = raw25791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25791; decide +kernel
    rw [ha]
    exact (canonical25791 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1776 + difference 5 4) (sourceB1776 + difference 4 5) sourceC1776) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1776 + difference 5 4) (sourceB1776 + difference 4 5) sourceC1776) = raw25792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1776 sourceB1776 sourceC1776 difference raw25792; decide +kernel
    rw [ha]
    exact (canonical25792 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1776 sourceB1776 sourceC1776
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1776, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1777 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1777 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1777 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceForm1777 : Integer.Sparse Master := [(Sum.inr 4119, 2), (Sum.inr 4121, 1), (Sum.inr 4122, 1), (Sum.inr 4133, 1), (Sum.inr 4301, 2), (Sum.inr 4303, 2), (Sum.inr 4304, 2), (Sum.inr 4314, 2), (Sum.inr 4424, 2), (Sum.inr 4428, 1), (Sum.inr 4431, 1), (Sum.inr 4458, 2), (Sum.inr 4460, 1), (Sum.inr 4467, 1), (Sum.inr 4495, 2), (Sum.inr 4496, 1), (Sum.inr 4499, 1), (Sum.inr 5102, 2), (Sum.inr 5275, 1), (Sum.inr 5293, 1), (Sum.inr 5306, 1)]

theorem sourceEq1777 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1777 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1777 + difference 0 1) (sourceB1777 + difference 1 0) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1777 + difference 0 1) (sourceB1777 + difference 1 0) sourceC1777) = raw7876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw7876; decide +kernel
    rw [ha]
    exact (canonical7876 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1777 + difference 0 2) (sourceB1777 + difference 2 0) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1777 + difference 0 2) (sourceB1777 + difference 2 0) sourceC1777) = raw7877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw7877; decide +kernel
    rw [ha]
    exact (canonical7877 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1777 + difference 0 3) (sourceB1777 + difference 3 0) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1777 + difference 0 3) (sourceB1777 + difference 3 0) sourceC1777) = raw3256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw3256; decide +kernel
    rw [ha]
    exact (canonical3256 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1777 + difference 0 4) (sourceB1777 + difference 4 0) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1777 + difference 0 4) (sourceB1777 + difference 4 0) sourceC1777) = raw7878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw7878; decide +kernel
    rw [ha]
    exact (canonical7878 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1777 + difference 0 5) (sourceB1777 + difference 5 0) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA1777 + difference 0 5) (sourceB1777 + difference 5 0) sourceC1777) = raw3246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw3246; decide +kernel
    rw [ha]
    exact (canonical3246 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1777 + difference 1 0) (sourceB1777 + difference 0 1) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1777 + difference 1 0) (sourceB1777 + difference 0 1) sourceC1777) = raw25793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25793; decide +kernel
    rw [ha]
    exact (canonical25793 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1777 + difference 1 2) (sourceB1777 + difference 2 1) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA1777 + difference 1 2) (sourceB1777 + difference 2 1) sourceC1777) = raw25794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25794; decide +kernel
    rw [ha]
    exact (canonical25794 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1777 + difference 1 3) (sourceB1777 + difference 3 1) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1777 + difference 1 3) (sourceB1777 + difference 3 1) sourceC1777) = raw7867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw7867; decide +kernel
    rw [ha]
    exact (canonical7867 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1777 + difference 1 4) (sourceB1777 + difference 4 1) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1777 + difference 1 4) (sourceB1777 + difference 4 1) sourceC1777) = raw25795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25795; decide +kernel
    rw [ha]
    exact (canonical25795 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1777 + difference 1 5) (sourceB1777 + difference 5 1) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1777 + difference 1 5) (sourceB1777 + difference 5 1) sourceC1777) = raw25796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25796; decide +kernel
    rw [ha]
    exact (canonical25796 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1777 + difference 2 0) (sourceB1777 + difference 0 2) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1777 + difference 2 0) (sourceB1777 + difference 0 2) sourceC1777) = raw25797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25797; decide +kernel
    rw [ha]
    exact (canonical25797 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1777 + difference 2 1) (sourceB1777 + difference 1 2) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA1777 + difference 2 1) (sourceB1777 + difference 1 2) sourceC1777) = raw25798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25798; decide +kernel
    rw [ha]
    exact (canonical25798 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1777 + difference 2 3) (sourceB1777 + difference 3 2) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1777 + difference 2 3) (sourceB1777 + difference 3 2) sourceC1777) = raw7871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw7871; decide +kernel
    rw [ha]
    exact (canonical7871 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1777 + difference 2 4) (sourceB1777 + difference 4 2) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1777 + difference 2 4) (sourceB1777 + difference 4 2) sourceC1777) = raw25799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25799; decide +kernel
    rw [ha]
    exact (canonical25799 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1777 + difference 2 5) (sourceB1777 + difference 5 2) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1777 + difference 2 5) (sourceB1777 + difference 5 2) sourceC1777) = raw25800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25800; decide +kernel
    rw [ha]
    exact (canonical25800 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1777 + difference 3 0) (sourceB1777 + difference 0 3) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4122) := by
    have ha : (tripleCharges (sourceA1777 + difference 3 0) (sourceB1777 + difference 0 3) sourceC1777) = raw25801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25801; decide +kernel
    rw [ha]
    exact (canonical25801 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1777 + difference 3 1) (sourceB1777 + difference 1 3) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA1777 + difference 3 1) (sourceB1777 + difference 1 3) sourceC1777) = raw25802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25802; decide +kernel
    rw [ha]
    exact (canonical25802 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1777 + difference 3 2) (sourceB1777 + difference 2 3) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA1777 + difference 3 2) (sourceB1777 + difference 2 3) sourceC1777) = raw25803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25803; decide +kernel
    rw [ha]
    exact (canonical25803 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1777 + difference 3 4) (sourceB1777 + difference 4 3) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1777 + difference 3 4) (sourceB1777 + difference 4 3) sourceC1777) = raw25804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25804; decide +kernel
    rw [ha]
    exact (canonical25804 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1777 + difference 3 5) (sourceB1777 + difference 5 3) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1777 + difference 3 5) (sourceB1777 + difference 5 3) sourceC1777) = raw25805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25805; decide +kernel
    rw [ha]
    exact (canonical25805 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1777 + difference 4 0) (sourceB1777 + difference 0 4) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4133) := by
    have ha : (tripleCharges (sourceA1777 + difference 4 0) (sourceB1777 + difference 0 4) sourceC1777) = raw25806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25806; decide +kernel
    rw [ha]
    exact (canonical25806 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1777 + difference 4 1) (sourceB1777 + difference 1 4) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4314) := by
    have ha : (tripleCharges (sourceA1777 + difference 4 1) (sourceB1777 + difference 1 4) sourceC1777) = raw25807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25807; decide +kernel
    rw [ha]
    exact (canonical25807 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1777 + difference 4 2) (sourceB1777 + difference 2 4) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4314) := by
    have ha : (tripleCharges (sourceA1777 + difference 4 2) (sourceB1777 + difference 2 4) sourceC1777) = raw25808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25808; decide +kernel
    rw [ha]
    exact (canonical25808 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1777 + difference 4 3) (sourceB1777 + difference 3 4) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1777 + difference 4 3) (sourceB1777 + difference 3 4) sourceC1777) = raw7879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw7879; decide +kernel
    rw [ha]
    exact (canonical7879 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1777 + difference 4 5) (sourceB1777 + difference 5 4) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1777 + difference 4 5) (sourceB1777 + difference 5 4) sourceC1777) = raw25809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25809; decide +kernel
    rw [ha]
    exact (canonical25809 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1777 + difference 5 0) (sourceB1777 + difference 0 5) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4121) := by
    have ha : (tripleCharges (sourceA1777 + difference 5 0) (sourceB1777 + difference 0 5) sourceC1777) = raw25810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25810; decide +kernel
    rw [ha]
    exact (canonical25810 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1777 + difference 5 1) (sourceB1777 + difference 1 5) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4303) := by
    have ha : (tripleCharges (sourceA1777 + difference 5 1) (sourceB1777 + difference 1 5) sourceC1777) = raw25811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25811; decide +kernel
    rw [ha]
    exact (canonical25811 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1777 + difference 5 2) (sourceB1777 + difference 2 5) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4303) := by
    have ha : (tripleCharges (sourceA1777 + difference 5 2) (sourceB1777 + difference 2 5) sourceC1777) = raw25812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25812; decide +kernel
    rw [ha]
    exact (canonical25812 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1777 + difference 5 3) (sourceB1777 + difference 3 5) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1777 + difference 5 3) (sourceB1777 + difference 3 5) sourceC1777) = raw7883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw7883; decide +kernel
    rw [ha]
    exact (canonical7883 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1777 + difference 5 4) (sourceB1777 + difference 4 5) sourceC1777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1777 + difference 5 4) (sourceB1777 + difference 4 5) sourceC1777) = raw25813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1777 sourceB1777 sourceC1777 difference raw25813; decide +kernel
    rw [ha]
    exact (canonical25813 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1777 sourceB1777 sourceC1777
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1777, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1778 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1778 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1778 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceForm1778 : Integer.Sparse Master := [(Sum.inr 554, 2), (Sum.inr 555, 1), (Sum.inr 556, 1), (Sum.inr 563, 1), (Sum.inr 879, 2), (Sum.inr 881, 2), (Sum.inr 882, 2), (Sum.inr 892, 2), (Sum.inr 1005, 2), (Sum.inr 1009, 1), (Sum.inr 1012, 1), (Sum.inr 1041, 2), (Sum.inr 1043, 1), (Sum.inr 1050, 1), (Sum.inr 1079, 2), (Sum.inr 1080, 1), (Sum.inr 1083, 1), (Sum.inr 2512, 2), (Sum.inr 2743, 1), (Sum.inr 2767, 1), (Sum.inr 2784, 1)]

theorem sourceEq1778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1778 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1778 + difference 0 1) (sourceB1778 + difference 1 0) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA1778 + difference 0 1) (sourceB1778 + difference 1 0) sourceC1778) = raw7904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw7904; decide +kernel
    rw [ha]
    exact (canonical7904 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1778 + difference 0 2) (sourceB1778 + difference 2 0) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA1778 + difference 0 2) (sourceB1778 + difference 2 0) sourceC1778) = raw7905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw7905; decide +kernel
    rw [ha]
    exact (canonical7905 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1778 + difference 0 3) (sourceB1778 + difference 3 0) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA1778 + difference 0 3) (sourceB1778 + difference 3 0) sourceC1778) = raw25814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25814; decide +kernel
    rw [ha]
    exact (canonical25814 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1778 + difference 0 4) (sourceB1778 + difference 4 0) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA1778 + difference 0 4) (sourceB1778 + difference 4 0) sourceC1778) = raw7906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw7906; decide +kernel
    rw [ha]
    exact (canonical7906 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1778 + difference 0 5) (sourceB1778 + difference 5 0) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA1778 + difference 0 5) (sourceB1778 + difference 5 0) sourceC1778) = raw7907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw7907; decide +kernel
    rw [ha]
    exact (canonical7907 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1778 + difference 1 0) (sourceB1778 + difference 0 1) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 554) := by
    have ha : (tripleCharges (sourceA1778 + difference 1 0) (sourceB1778 + difference 0 1) sourceC1778) = raw25815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25815; decide +kernel
    rw [ha]
    exact (canonical25815 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1778 + difference 1 2) (sourceB1778 + difference 2 1) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 879) := by
    have ha : (tripleCharges (sourceA1778 + difference 1 2) (sourceB1778 + difference 2 1) sourceC1778) = raw25816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25816; decide +kernel
    rw [ha]
    exact (canonical25816 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1778 + difference 1 3) (sourceB1778 + difference 3 1) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1778 + difference 1 3) (sourceB1778 + difference 3 1) sourceC1778) = raw7893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw7893; decide +kernel
    rw [ha]
    exact (canonical7893 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1778 + difference 1 4) (sourceB1778 + difference 4 1) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1778 + difference 1 4) (sourceB1778 + difference 4 1) sourceC1778) = raw25817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25817; decide +kernel
    rw [ha]
    exact (canonical25817 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1778 + difference 1 5) (sourceB1778 + difference 5 1) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1778 + difference 1 5) (sourceB1778 + difference 5 1) sourceC1778) = raw25818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25818; decide +kernel
    rw [ha]
    exact (canonical25818 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1778 + difference 2 0) (sourceB1778 + difference 0 2) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 554) := by
    have ha : (tripleCharges (sourceA1778 + difference 2 0) (sourceB1778 + difference 0 2) sourceC1778) = raw25819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25819; decide +kernel
    rw [ha]
    exact (canonical25819 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1778 + difference 2 1) (sourceB1778 + difference 1 2) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 879) := by
    have ha : (tripleCharges (sourceA1778 + difference 2 1) (sourceB1778 + difference 1 2) sourceC1778) = raw25820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25820; decide +kernel
    rw [ha]
    exact (canonical25820 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1778 + difference 2 3) (sourceB1778 + difference 3 2) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1778 + difference 2 3) (sourceB1778 + difference 3 2) sourceC1778) = raw7898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw7898; decide +kernel
    rw [ha]
    exact (canonical7898 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1778 + difference 2 4) (sourceB1778 + difference 4 2) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1778 + difference 2 4) (sourceB1778 + difference 4 2) sourceC1778) = raw25821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25821; decide +kernel
    rw [ha]
    exact (canonical25821 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1778 + difference 2 5) (sourceB1778 + difference 5 2) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1778 + difference 2 5) (sourceB1778 + difference 5 2) sourceC1778) = raw25822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25822; decide +kernel
    rw [ha]
    exact (canonical25822 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1778 + difference 3 0) (sourceB1778 + difference 0 3) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 556) := by
    have ha : (tripleCharges (sourceA1778 + difference 3 0) (sourceB1778 + difference 0 3) sourceC1778) = raw25823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25823; decide +kernel
    rw [ha]
    exact (canonical25823 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1778 + difference 3 1) (sourceB1778 + difference 1 3) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA1778 + difference 3 1) (sourceB1778 + difference 1 3) sourceC1778) = raw25824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25824; decide +kernel
    rw [ha]
    exact (canonical25824 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1778 + difference 3 2) (sourceB1778 + difference 2 3) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA1778 + difference 3 2) (sourceB1778 + difference 2 3) sourceC1778) = raw25825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25825; decide +kernel
    rw [ha]
    exact (canonical25825 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1778 + difference 3 4) (sourceB1778 + difference 4 3) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1778 + difference 3 4) (sourceB1778 + difference 4 3) sourceC1778) = raw25826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25826; decide +kernel
    rw [ha]
    exact (canonical25826 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1778 + difference 3 5) (sourceB1778 + difference 5 3) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1778 + difference 3 5) (sourceB1778 + difference 5 3) sourceC1778) = raw25827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25827; decide +kernel
    rw [ha]
    exact (canonical25827 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1778 + difference 4 0) (sourceB1778 + difference 0 4) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 563) := by
    have ha : (tripleCharges (sourceA1778 + difference 4 0) (sourceB1778 + difference 0 4) sourceC1778) = raw25828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25828; decide +kernel
    rw [ha]
    exact (canonical25828 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1778 + difference 4 1) (sourceB1778 + difference 1 4) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 892) := by
    have ha : (tripleCharges (sourceA1778 + difference 4 1) (sourceB1778 + difference 1 4) sourceC1778) = raw25829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25829; decide +kernel
    rw [ha]
    exact (canonical25829 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1778 + difference 4 2) (sourceB1778 + difference 2 4) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 892) := by
    have ha : (tripleCharges (sourceA1778 + difference 4 2) (sourceB1778 + difference 2 4) sourceC1778) = raw25830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25830; decide +kernel
    rw [ha]
    exact (canonical25830 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1778 + difference 4 3) (sourceB1778 + difference 3 4) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1778 + difference 4 3) (sourceB1778 + difference 3 4) sourceC1778) = raw7908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw7908; decide +kernel
    rw [ha]
    exact (canonical7908 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1778 + difference 4 5) (sourceB1778 + difference 5 4) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1778 + difference 4 5) (sourceB1778 + difference 5 4) sourceC1778) = raw25831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25831; decide +kernel
    rw [ha]
    exact (canonical25831 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1778 + difference 5 0) (sourceB1778 + difference 0 5) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 555) := by
    have ha : (tripleCharges (sourceA1778 + difference 5 0) (sourceB1778 + difference 0 5) sourceC1778) = raw25832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25832; decide +kernel
    rw [ha]
    exact (canonical25832 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1778 + difference 5 1) (sourceB1778 + difference 1 5) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 881) := by
    have ha : (tripleCharges (sourceA1778 + difference 5 1) (sourceB1778 + difference 1 5) sourceC1778) = raw25833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25833; decide +kernel
    rw [ha]
    exact (canonical25833 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1778 + difference 5 2) (sourceB1778 + difference 2 5) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 881) := by
    have ha : (tripleCharges (sourceA1778 + difference 5 2) (sourceB1778 + difference 2 5) sourceC1778) = raw25834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25834; decide +kernel
    rw [ha]
    exact (canonical25834 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1778 + difference 5 3) (sourceB1778 + difference 3 5) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1778 + difference 5 3) (sourceB1778 + difference 3 5) sourceC1778) = raw7913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw7913; decide +kernel
    rw [ha]
    exact (canonical7913 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1778 + difference 5 4) (sourceB1778 + difference 4 5) sourceC1778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1778 + difference 5 4) (sourceB1778 + difference 4 5) sourceC1778) = raw25835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1778 sourceB1778 sourceC1778 difference raw25835; decide +kernel
    rw [ha]
    exact (canonical25835 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1778 sourceB1778 sourceC1778
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1778, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1779 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB1779 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1779 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1779 : Integer.Sparse Master := [(Sum.inr 4265, 2), (Sum.inr 4270, 1), (Sum.inr 4273, 1), (Sum.inr 4283, 1), (Sum.inr 4397, 2), (Sum.inr 4419, 2), (Sum.inr 4420, 2), (Sum.inr 4424, 2), (Sum.inr 4453, 2), (Sum.inr 4458, 2), (Sum.inr 4459, 2), (Sum.inr 4491, 1), (Sum.inr 4492, 1), (Sum.inr 4498, 1), (Sum.inr 4500, 1), (Sum.inr 4502, 1), (Sum.inr 4503, 1), (Sum.inr 4603, 2), (Sum.inr 4619, 1), (Sum.inr 4620, 1), (Sum.inr 4624, 1)]

theorem sourceEq1779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1779 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1779 + difference 0 1) (sourceB1779 + difference 1 0) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1779 + difference 0 1) (sourceB1779 + difference 1 0) sourceC1779) = raw25836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25836; decide +kernel
    rw [ha]
    exact (canonical25836 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1779 + difference 0 2) (sourceB1779 + difference 2 0) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1779 + difference 0 2) (sourceB1779 + difference 2 0) sourceC1779) = raw24612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw24612; decide +kernel
    rw [ha]
    exact (canonical24612 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1779 + difference 0 3) (sourceB1779 + difference 3 0) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1779 + difference 0 3) (sourceB1779 + difference 3 0) sourceC1779) = raw24171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw24171; decide +kernel
    rw [ha]
    exact (canonical24171 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1779 + difference 0 4) (sourceB1779 + difference 4 0) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4620) := by
    have ha : (tripleCharges (sourceA1779 + difference 0 4) (sourceB1779 + difference 4 0) sourceC1779) = raw25837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25837; decide +kernel
    rw [ha]
    exact (canonical25837 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1779 + difference 0 5) (sourceB1779 + difference 5 0) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1779 + difference 0 5) (sourceB1779 + difference 5 0) sourceC1779) = raw25698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25698; decide +kernel
    rw [ha]
    exact (canonical25698 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1779 + difference 1 0) (sourceB1779 + difference 0 1) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1779 + difference 1 0) (sourceB1779 + difference 0 1) sourceC1779) = raw25281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25281; decide +kernel
    rw [ha]
    exact (canonical25281 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1779 + difference 1 2) (sourceB1779 + difference 2 1) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4397) := by
    have ha : (tripleCharges (sourceA1779 + difference 1 2) (sourceB1779 + difference 2 1) sourceC1779) = raw25283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25283; decide +kernel
    rw [ha]
    exact (canonical25283 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1779 + difference 1 3) (sourceB1779 + difference 3 1) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1779 + difference 1 3) (sourceB1779 + difference 3 1) sourceC1779) = raw25108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25108; decide +kernel
    rw [ha]
    exact (canonical25108 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1779 + difference 1 4) (sourceB1779 + difference 4 1) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA1779 + difference 1 4) (sourceB1779 + difference 4 1) sourceC1779) = raw25284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25284; decide +kernel
    rw [ha]
    exact (canonical25284 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1779 + difference 1 5) (sourceB1779 + difference 5 1) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1779 + difference 1 5) (sourceB1779 + difference 5 1) sourceC1779) = raw25102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25102; decide +kernel
    rw [ha]
    exact (canonical25102 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1779 + difference 2 0) (sourceB1779 + difference 0 2) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1779 + difference 2 0) (sourceB1779 + difference 0 2) sourceC1779) = raw25838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25838; decide +kernel
    rw [ha]
    exact (canonical25838 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1779 + difference 2 1) (sourceB1779 + difference 1 2) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4397) := by
    have ha : (tripleCharges (sourceA1779 + difference 2 1) (sourceB1779 + difference 1 2) sourceC1779) = raw25839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25839; decide +kernel
    rw [ha]
    exact (canonical25839 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1779 + difference 2 3) (sourceB1779 + difference 3 2) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1779 + difference 2 3) (sourceB1779 + difference 3 2) sourceC1779) = raw25278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25278; decide +kernel
    rw [ha]
    exact (canonical25278 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1779 + difference 2 4) (sourceB1779 + difference 4 2) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA1779 + difference 2 4) (sourceB1779 + difference 4 2) sourceC1779) = raw25840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25840; decide +kernel
    rw [ha]
    exact (canonical25840 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1779 + difference 2 5) (sourceB1779 + difference 5 2) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1779 + difference 2 5) (sourceB1779 + difference 5 2) sourceC1779) = raw25702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25702; decide +kernel
    rw [ha]
    exact (canonical25702 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1779 + difference 3 0) (sourceB1779 + difference 0 3) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1779 + difference 3 0) (sourceB1779 + difference 0 3) sourceC1779) = raw25841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25841; decide +kernel
    rw [ha]
    exact (canonical25841 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1779 + difference 3 1) (sourceB1779 + difference 1 3) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4420) := by
    have ha : (tripleCharges (sourceA1779 + difference 3 1) (sourceB1779 + difference 1 3) sourceC1779) = raw25842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25842; decide +kernel
    rw [ha]
    exact (canonical25842 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1779 + difference 3 2) (sourceB1779 + difference 2 3) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4420) := by
    have ha : (tripleCharges (sourceA1779 + difference 3 2) (sourceB1779 + difference 2 3) sourceC1779) = raw25843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25843; decide +kernel
    rw [ha]
    exact (canonical25843 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1779 + difference 3 4) (sourceB1779 + difference 4 3) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4492) := by
    have ha : (tripleCharges (sourceA1779 + difference 3 4) (sourceB1779 + difference 4 3) sourceC1779) = raw25844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25844; decide +kernel
    rw [ha]
    exact (canonical25844 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1779 + difference 3 5) (sourceB1779 + difference 5 3) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA1779 + difference 3 5) (sourceB1779 + difference 5 3) sourceC1779) = raw25707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25707; decide +kernel
    rw [ha]
    exact (canonical25707 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1779 + difference 4 0) (sourceB1779 + difference 0 4) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4283) := by
    have ha : (tripleCharges (sourceA1779 + difference 4 0) (sourceB1779 + difference 0 4) sourceC1779) = raw25713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25713; decide +kernel
    rw [ha]
    exact (canonical25713 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1779 + difference 4 1) (sourceB1779 + difference 1 4) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1779 + difference 4 1) (sourceB1779 + difference 1 4) sourceC1779) = raw25714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25714; decide +kernel
    rw [ha]
    exact (canonical25714 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1779 + difference 4 2) (sourceB1779 + difference 2 4) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1779 + difference 4 2) (sourceB1779 + difference 2 4) sourceC1779) = raw24609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw24609; decide +kernel
    rw [ha]
    exact (canonical24609 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1779 + difference 4 3) (sourceB1779 + difference 3 4) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1779 + difference 4 3) (sourceB1779 + difference 3 4) sourceC1779) = raw24260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw24260; decide +kernel
    rw [ha]
    exact (canonical24260 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1779 + difference 4 5) (sourceB1779 + difference 5 4) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1779 + difference 4 5) (sourceB1779 + difference 5 4) sourceC1779) = raw25100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25100; decide +kernel
    rw [ha]
    exact (canonical25100 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1779 + difference 5 0) (sourceB1779 + difference 0 5) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1779 + difference 5 0) (sourceB1779 + difference 0 5) sourceC1779) = raw25845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25845; decide +kernel
    rw [ha]
    exact (canonical25845 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1779 + difference 5 1) (sourceB1779 + difference 1 5) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1779 + difference 5 1) (sourceB1779 + difference 1 5) sourceC1779) = raw25846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25846; decide +kernel
    rw [ha]
    exact (canonical25846 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1779 + difference 5 2) (sourceB1779 + difference 2 5) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1779 + difference 5 2) (sourceB1779 + difference 2 5) sourceC1779) = raw24818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw24818; decide +kernel
    rw [ha]
    exact (canonical24818 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1779 + difference 5 3) (sourceB1779 + difference 3 5) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1779 + difference 5 3) (sourceB1779 + difference 3 5) sourceC1779) = raw24167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw24167; decide +kernel
    rw [ha]
    exact (canonical24167 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1779 + difference 5 4) (sourceB1779 + difference 4 5) sourceC1779) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA1779 + difference 5 4) (sourceB1779 + difference 4 5) sourceC1779) = raw25847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1779 sourceB1779 sourceC1779 difference raw25847; decide +kernel
    rw [ha]
    exact (canonical25847 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1779 sourceB1779 sourceC1779
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1779, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1780 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1780 : Charge := ![1, 0, 0, 1, -2, 0]
def sourceC1780 : Charge := ![3, 0, 0, -2, 1, -2]
def sourceForm1780 : Integer.Sparse Master := [(Sum.inr 1075, 1), (Sum.inr 2048, 2), (Sum.inr 2229, 1), (Sum.inr 2276, 1), (Sum.inr 2288, 1), (Sum.inr 4082, -1)]

theorem sourceEq1780 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1780 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 0) (sourceB1780 + difference 0 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 0) (sourceB1780 + difference 0 0) sourceC1780) = raw25848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25848; decide +kernel
    rw [ha]
    exact (canonical25848 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 1) (sourceB1780 + difference 1 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 1) (sourceB1780 + difference 1 0) sourceC1780) = raw25849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25849; decide +kernel
    rw [ha]
    exact (canonical25849 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 2) (sourceB1780 + difference 2 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 2) (sourceB1780 + difference 2 0) sourceC1780) = raw25850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25850; decide +kernel
    rw [ha]
    exact (canonical25850 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 3) (sourceB1780 + difference 3 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 3) (sourceB1780 + difference 3 0) sourceC1780) = raw25851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25851; decide +kernel
    rw [ha]
    exact (canonical25851 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 4) (sourceB1780 + difference 4 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 4) (sourceB1780 + difference 4 0) sourceC1780) = raw25852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25852; decide +kernel
    rw [ha]
    exact (canonical25852 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1780 + difference 0 5) (sourceB1780 + difference 5 0) sourceC1780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA1780 + difference 0 5) (sourceB1780 + difference 5 0) sourceC1780) = raw25853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1780 sourceB1780 sourceC1780 difference raw25853; decide +kernel
    rw [ha]
    exact (canonical25853 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1780 + sourceB1780) sourceC1780) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1780 + sourceB1780) sourceC1780) = raw25854 := by
      apply Matrix.ext; unfold doubleCharges sourceA1780 sourceB1780 sourceC1780 raw25854; decide +kernel
    rw [ha]
    exact (canonical25854 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1780 sourceB1780 sourceC1780
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1780, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1781 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1781 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1781 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceForm1781 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4175, 2), (Sum.inr 4183, 1), (Sum.inr 4186, 2), (Sum.inr 4344, 2), (Sum.inr 4352, 2), (Sum.inr 4355, 4), (Sum.inr 4458, 4), (Sum.inr 4463, 2), (Sum.inr 4467, 2), (Sum.inr 4497, 2), (Sum.inr 4502, 2), (Sum.inr 4838, 2), (Sum.inr 4895, 2)]

theorem sourceEq1781 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1781 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1781 + difference 0 1) (sourceB1781 + difference 1 0) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA1781 + difference 0 1) (sourceB1781 + difference 1 0) sourceC1781) = raw25855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25855; decide +kernel
    rw [ha]
    exact (canonical25855 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1781 + difference 0 2) (sourceB1781 + difference 2 0) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA1781 + difference 0 2) (sourceB1781 + difference 2 0) sourceC1781) = raw25856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25856; decide +kernel
    rw [ha]
    exact (canonical25856 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1781 + difference 0 3) (sourceB1781 + difference 3 0) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1781 + difference 0 3) (sourceB1781 + difference 3 0) sourceC1781) = raw25857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25857; decide +kernel
    rw [ha]
    exact (canonical25857 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1781 + difference 0 4) (sourceB1781 + difference 4 0) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1781 + difference 0 4) (sourceB1781 + difference 4 0) sourceC1781) = raw25858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25858; decide +kernel
    rw [ha]
    exact (canonical25858 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1781 + difference 0 5) (sourceB1781 + difference 5 0) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1781 + difference 0 5) (sourceB1781 + difference 5 0) sourceC1781) = raw25859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25859; decide +kernel
    rw [ha]
    exact (canonical25859 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1781 + difference 1 0) (sourceB1781 + difference 0 1) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1781 + difference 1 0) (sourceB1781 + difference 0 1) sourceC1781) = raw25860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25860; decide +kernel
    rw [ha]
    exact (canonical25860 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1781 + difference 1 2) (sourceB1781 + difference 2 1) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1781 + difference 1 2) (sourceB1781 + difference 2 1) sourceC1781) = raw25861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25861; decide +kernel
    rw [ha]
    exact (canonical25861 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1781 + difference 1 3) (sourceB1781 + difference 3 1) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1781 + difference 1 3) (sourceB1781 + difference 3 1) sourceC1781) = raw25862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25862; decide +kernel
    rw [ha]
    exact (canonical25862 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1781 + difference 1 4) (sourceB1781 + difference 4 1) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1781 + difference 1 4) (sourceB1781 + difference 4 1) sourceC1781) = raw25863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25863; decide +kernel
    rw [ha]
    exact (canonical25863 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1781 + difference 1 5) (sourceB1781 + difference 5 1) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1781 + difference 1 5) (sourceB1781 + difference 5 1) sourceC1781) = raw25864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25864; decide +kernel
    rw [ha]
    exact (canonical25864 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1781 + difference 2 0) (sourceB1781 + difference 0 2) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1781 + difference 2 0) (sourceB1781 + difference 0 2) sourceC1781) = raw25865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25865; decide +kernel
    rw [ha]
    exact (canonical25865 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1781 + difference 2 1) (sourceB1781 + difference 1 2) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1781 + difference 2 1) (sourceB1781 + difference 1 2) sourceC1781) = raw25866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25866; decide +kernel
    rw [ha]
    exact (canonical25866 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1781 + difference 2 3) (sourceB1781 + difference 3 2) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1781 + difference 2 3) (sourceB1781 + difference 3 2) sourceC1781) = raw25867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25867; decide +kernel
    rw [ha]
    exact (canonical25867 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1781 + difference 2 4) (sourceB1781 + difference 4 2) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1781 + difference 2 4) (sourceB1781 + difference 4 2) sourceC1781) = raw25868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25868; decide +kernel
    rw [ha]
    exact (canonical25868 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1781 + difference 2 5) (sourceB1781 + difference 5 2) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1781 + difference 2 5) (sourceB1781 + difference 5 2) sourceC1781) = raw25869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25869; decide +kernel
    rw [ha]
    exact (canonical25869 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1781 + difference 3 0) (sourceB1781 + difference 0 3) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4186) := by
    have ha : (tripleCharges (sourceA1781 + difference 3 0) (sourceB1781 + difference 0 3) sourceC1781) = raw25870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25870; decide +kernel
    rw [ha]
    exact (canonical25870 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1781 + difference 3 1) (sourceB1781 + difference 1 3) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1781 + difference 3 1) (sourceB1781 + difference 1 3) sourceC1781) = raw25871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25871; decide +kernel
    rw [ha]
    exact (canonical25871 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1781 + difference 3 2) (sourceB1781 + difference 2 3) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1781 + difference 3 2) (sourceB1781 + difference 2 3) sourceC1781) = raw25872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25872; decide +kernel
    rw [ha]
    exact (canonical25872 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1781 + difference 3 4) (sourceB1781 + difference 4 3) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1781 + difference 3 4) (sourceB1781 + difference 4 3) sourceC1781) = raw25873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25873; decide +kernel
    rw [ha]
    exact (canonical25873 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1781 + difference 3 5) (sourceB1781 + difference 5 3) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1781 + difference 3 5) (sourceB1781 + difference 5 3) sourceC1781) = raw25874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25874; decide +kernel
    rw [ha]
    exact (canonical25874 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1781 + difference 4 0) (sourceB1781 + difference 0 4) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4186) := by
    have ha : (tripleCharges (sourceA1781 + difference 4 0) (sourceB1781 + difference 0 4) sourceC1781) = raw25875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25875; decide +kernel
    rw [ha]
    exact (canonical25875 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1781 + difference 4 1) (sourceB1781 + difference 1 4) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1781 + difference 4 1) (sourceB1781 + difference 1 4) sourceC1781) = raw25876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25876; decide +kernel
    rw [ha]
    exact (canonical25876 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1781 + difference 4 2) (sourceB1781 + difference 2 4) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1781 + difference 4 2) (sourceB1781 + difference 2 4) sourceC1781) = raw25877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25877; decide +kernel
    rw [ha]
    exact (canonical25877 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1781 + difference 4 3) (sourceB1781 + difference 3 4) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1781 + difference 4 3) (sourceB1781 + difference 3 4) sourceC1781) = raw25878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25878; decide +kernel
    rw [ha]
    exact (canonical25878 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1781 + difference 4 5) (sourceB1781 + difference 5 4) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1781 + difference 4 5) (sourceB1781 + difference 5 4) sourceC1781) = raw25879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25879; decide +kernel
    rw [ha]
    exact (canonical25879 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1781 + difference 5 0) (sourceB1781 + difference 0 5) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4183) := by
    have ha : (tripleCharges (sourceA1781 + difference 5 0) (sourceB1781 + difference 0 5) sourceC1781) = raw25880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25880; decide +kernel
    rw [ha]
    exact (canonical25880 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1781 + difference 5 1) (sourceB1781 + difference 1 5) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1781 + difference 5 1) (sourceB1781 + difference 1 5) sourceC1781) = raw25881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25881; decide +kernel
    rw [ha]
    exact (canonical25881 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1781 + difference 5 2) (sourceB1781 + difference 2 5) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1781 + difference 5 2) (sourceB1781 + difference 2 5) sourceC1781) = raw25882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25882; decide +kernel
    rw [ha]
    exact (canonical25882 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1781 + difference 5 3) (sourceB1781 + difference 3 5) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1781 + difference 5 3) (sourceB1781 + difference 3 5) sourceC1781) = raw25883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25883; decide +kernel
    rw [ha]
    exact (canonical25883 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1781 + difference 5 4) (sourceB1781 + difference 4 5) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1781 + difference 5 4) (sourceB1781 + difference 4 5) sourceC1781) = raw25884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25884; decide +kernel
    rw [ha]
    exact (canonical25884 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1781 sourceB1781 sourceC1781
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1781, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1782 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1782 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1782 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceForm1782 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4172, 2), (Sum.inr 4177, 1), (Sum.inr 4180, 1), (Sum.inr 4185, 1), (Sum.inr 4341, 2), (Sum.inr 4346, 2), (Sum.inr 4349, 2), (Sum.inr 4354, 2), (Sum.inr 4457, 2), (Sum.inr 4460, 1), (Sum.inr 4466, 1), (Sum.inr 4495, 2), (Sum.inr 4498, 2), (Sum.inr 4499, 1), (Sum.inr 4503, 1), (Sum.inr 4505, 1), (Sum.inr 4511, 1), (Sum.inr 4834, 2), (Sum.inr 4894, 1), (Sum.inr 4895, 1)]

theorem sourceEq1782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1782 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1782 + difference 0 1) (sourceB1782 + difference 1 0) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA1782 + difference 0 1) (sourceB1782 + difference 1 0) sourceC1782) = raw25885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25885; decide +kernel
    rw [ha]
    exact (canonical25885 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1782 + difference 0 2) (sourceB1782 + difference 2 0) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA1782 + difference 0 2) (sourceB1782 + difference 2 0) sourceC1782) = raw25886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25886; decide +kernel
    rw [ha]
    exact (canonical25886 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1782 + difference 0 3) (sourceB1782 + difference 3 0) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA1782 + difference 0 3) (sourceB1782 + difference 3 0) sourceC1782) = raw25887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25887; decide +kernel
    rw [ha]
    exact (canonical25887 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1782 + difference 0 4) (sourceB1782 + difference 4 0) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1782 + difference 0 4) (sourceB1782 + difference 4 0) sourceC1782) = raw25888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25888; decide +kernel
    rw [ha]
    exact (canonical25888 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1782 + difference 0 5) (sourceB1782 + difference 5 0) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1782 + difference 0 5) (sourceB1782 + difference 5 0) sourceC1782) = raw25889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25889; decide +kernel
    rw [ha]
    exact (canonical25889 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1782 + difference 1 0) (sourceB1782 + difference 0 1) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1782 + difference 1 0) (sourceB1782 + difference 0 1) sourceC1782) = raw25890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25890; decide +kernel
    rw [ha]
    exact (canonical25890 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1782 + difference 1 2) (sourceB1782 + difference 2 1) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1782 + difference 1 2) (sourceB1782 + difference 2 1) sourceC1782) = raw25891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25891; decide +kernel
    rw [ha]
    exact (canonical25891 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1782 + difference 1 3) (sourceB1782 + difference 3 1) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1782 + difference 1 3) (sourceB1782 + difference 3 1) sourceC1782) = raw25892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25892; decide +kernel
    rw [ha]
    exact (canonical25892 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1782 + difference 1 4) (sourceB1782 + difference 4 1) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1782 + difference 1 4) (sourceB1782 + difference 4 1) sourceC1782) = raw25893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25893; decide +kernel
    rw [ha]
    exact (canonical25893 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1782 + difference 1 5) (sourceB1782 + difference 5 1) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1782 + difference 1 5) (sourceB1782 + difference 5 1) sourceC1782) = raw25894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25894; decide +kernel
    rw [ha]
    exact (canonical25894 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1782 + difference 2 0) (sourceB1782 + difference 0 2) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1782 + difference 2 0) (sourceB1782 + difference 0 2) sourceC1782) = raw25895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25895; decide +kernel
    rw [ha]
    exact (canonical25895 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1782 + difference 2 1) (sourceB1782 + difference 1 2) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1782 + difference 2 1) (sourceB1782 + difference 1 2) sourceC1782) = raw25896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25896; decide +kernel
    rw [ha]
    exact (canonical25896 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1782 + difference 2 3) (sourceB1782 + difference 3 2) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1782 + difference 2 3) (sourceB1782 + difference 3 2) sourceC1782) = raw25897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25897; decide +kernel
    rw [ha]
    exact (canonical25897 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1782 + difference 2 4) (sourceB1782 + difference 4 2) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1782 + difference 2 4) (sourceB1782 + difference 4 2) sourceC1782) = raw25898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25898; decide +kernel
    rw [ha]
    exact (canonical25898 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1782 + difference 2 5) (sourceB1782 + difference 5 2) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1782 + difference 2 5) (sourceB1782 + difference 5 2) sourceC1782) = raw25899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25899; decide +kernel
    rw [ha]
    exact (canonical25899 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1782 + difference 3 0) (sourceB1782 + difference 0 3) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1782 + difference 3 0) (sourceB1782 + difference 0 3) sourceC1782) = raw25900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25900; decide +kernel
    rw [ha]
    exact (canonical25900 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1782 + difference 3 1) (sourceB1782 + difference 1 3) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1782 + difference 3 1) (sourceB1782 + difference 1 3) sourceC1782) = raw25901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25901; decide +kernel
    rw [ha]
    exact (canonical25901 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1782 + difference 3 2) (sourceB1782 + difference 2 3) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1782 + difference 3 2) (sourceB1782 + difference 2 3) sourceC1782) = raw25902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25902; decide +kernel
    rw [ha]
    exact (canonical25902 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1782 + difference 3 4) (sourceB1782 + difference 4 3) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1782 + difference 3 4) (sourceB1782 + difference 4 3) sourceC1782) = raw25903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25903; decide +kernel
    rw [ha]
    exact (canonical25903 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1782 + difference 3 5) (sourceB1782 + difference 5 3) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1782 + difference 3 5) (sourceB1782 + difference 5 3) sourceC1782) = raw25904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25904; decide +kernel
    rw [ha]
    exact (canonical25904 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1782 + difference 4 0) (sourceB1782 + difference 0 4) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4185) := by
    have ha : (tripleCharges (sourceA1782 + difference 4 0) (sourceB1782 + difference 0 4) sourceC1782) = raw25905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25905; decide +kernel
    rw [ha]
    exact (canonical25905 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1782 + difference 4 1) (sourceB1782 + difference 1 4) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1782 + difference 4 1) (sourceB1782 + difference 1 4) sourceC1782) = raw25906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25906; decide +kernel
    rw [ha]
    exact (canonical25906 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1782 + difference 4 2) (sourceB1782 + difference 2 4) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1782 + difference 4 2) (sourceB1782 + difference 2 4) sourceC1782) = raw25907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25907; decide +kernel
    rw [ha]
    exact (canonical25907 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1782 + difference 4 3) (sourceB1782 + difference 3 4) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1782 + difference 4 3) (sourceB1782 + difference 3 4) sourceC1782) = raw25908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25908; decide +kernel
    rw [ha]
    exact (canonical25908 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1782 + difference 4 5) (sourceB1782 + difference 5 4) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1782 + difference 4 5) (sourceB1782 + difference 5 4) sourceC1782) = raw25909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25909; decide +kernel
    rw [ha]
    exact (canonical25909 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1782 + difference 5 0) (sourceB1782 + difference 0 5) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1782 + difference 5 0) (sourceB1782 + difference 0 5) sourceC1782) = raw25910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25910; decide +kernel
    rw [ha]
    exact (canonical25910 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1782 + difference 5 1) (sourceB1782 + difference 1 5) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1782 + difference 5 1) (sourceB1782 + difference 1 5) sourceC1782) = raw25911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25911; decide +kernel
    rw [ha]
    exact (canonical25911 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1782 + difference 5 2) (sourceB1782 + difference 2 5) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1782 + difference 5 2) (sourceB1782 + difference 2 5) sourceC1782) = raw25912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25912; decide +kernel
    rw [ha]
    exact (canonical25912 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1782 + difference 5 3) (sourceB1782 + difference 3 5) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1782 + difference 5 3) (sourceB1782 + difference 3 5) sourceC1782) = raw25913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25913; decide +kernel
    rw [ha]
    exact (canonical25913 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1782 + difference 5 4) (sourceB1782 + difference 4 5) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1782 + difference 5 4) (sourceB1782 + difference 4 5) sourceC1782) = raw25914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25914; decide +kernel
    rw [ha]
    exact (canonical25914 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1782 sourceB1782 sourceC1782
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1782, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1783 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1783 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC1783 : Charge := ![3, 0, 0, -1, 1, -3]
def sourceForm1783 : Integer.Sparse Master := [(Sum.inr 1074, 1), (Sum.inr 2047, 2), (Sum.inr 2228, 1), (Sum.inr 2261, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

theorem sourceEq1783 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1783 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 0) (sourceB1783 + difference 0 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 0) (sourceB1783 + difference 0 0) sourceC1783) = raw25915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25915; decide +kernel
    rw [ha]
    exact (canonical25915 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 1) (sourceB1783 + difference 1 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2047) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 1) (sourceB1783 + difference 1 0) sourceC1783) = raw25916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25916; decide +kernel
    rw [ha]
    exact (canonical25916 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 2) (sourceB1783 + difference 2 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2047) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 2) (sourceB1783 + difference 2 0) sourceC1783) = raw25917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25917; decide +kernel
    rw [ha]
    exact (canonical25917 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 3) (sourceB1783 + difference 3 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 3) (sourceB1783 + difference 3 0) sourceC1783) = raw25918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25918; decide +kernel
    rw [ha]
    exact (canonical25918 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 4) (sourceB1783 + difference 4 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 4) (sourceB1783 + difference 4 0) sourceC1783) = raw25919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25919; decide +kernel
    rw [ha]
    exact (canonical25919 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1783 + difference 0 5) (sourceB1783 + difference 5 0) sourceC1783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1783 + difference 0 5) (sourceB1783 + difference 5 0) sourceC1783) = raw25920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1783 sourceB1783 sourceC1783 difference raw25920; decide +kernel
    rw [ha]
    exact (canonical25920 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1783 + sourceB1783) sourceC1783) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1783 + sourceB1783) sourceC1783) = raw25921 := by
      apply Matrix.ext; unfold doubleCharges sourceA1783 sourceB1783 sourceC1783 raw25921; decide +kernel
    rw [ha]
    exact (canonical25921 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1783 sourceB1783 sourceC1783
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1783, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1784 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1784 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1784 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1784 : Integer.Sparse Master := [(Sum.inr 4170, 2), (Sum.inr 4174, 1), (Sum.inr 4179, 2), (Sum.inr 4340, 2), (Sum.inr 4343, 2), (Sum.inr 4348, 4), (Sum.inr 4494, 2), (Sum.inr 4496, 4), (Sum.inr 4500, 2), (Sum.inr 4501, 2), (Sum.inr 4510, 2), (Sum.inr 4832, 2), (Sum.inr 4890, 1), (Sum.inr 4897, 2)]

theorem sourceEq1784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1784 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1784 + difference 0 1) (sourceB1784 + difference 1 0) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA1784 + difference 0 1) (sourceB1784 + difference 1 0) sourceC1784) = raw25922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25922; decide +kernel
    rw [ha]
    exact (canonical25922 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1784 + difference 0 2) (sourceB1784 + difference 2 0) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA1784 + difference 0 2) (sourceB1784 + difference 2 0) sourceC1784) = raw25923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25923; decide +kernel
    rw [ha]
    exact (canonical25923 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1784 + difference 0 3) (sourceB1784 + difference 3 0) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1784 + difference 0 3) (sourceB1784 + difference 3 0) sourceC1784) = raw21834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw21834; decide +kernel
    rw [ha]
    exact (canonical21834 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1784 + difference 0 4) (sourceB1784 + difference 4 0) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1784 + difference 0 4) (sourceB1784 + difference 4 0) sourceC1784) = raw25924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25924; decide +kernel
    rw [ha]
    exact (canonical25924 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1784 + difference 0 5) (sourceB1784 + difference 5 0) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1784 + difference 0 5) (sourceB1784 + difference 5 0) sourceC1784) = raw25925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25925; decide +kernel
    rw [ha]
    exact (canonical25925 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1784 + difference 1 0) (sourceB1784 + difference 0 1) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4170) := by
    have ha : (tripleCharges (sourceA1784 + difference 1 0) (sourceB1784 + difference 0 1) sourceC1784) = raw25926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25926; decide +kernel
    rw [ha]
    exact (canonical25926 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1784 + difference 1 2) (sourceB1784 + difference 2 1) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4340) := by
    have ha : (tripleCharges (sourceA1784 + difference 1 2) (sourceB1784 + difference 2 1) sourceC1784) = raw25927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25927; decide +kernel
    rw [ha]
    exact (canonical25927 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1784 + difference 1 3) (sourceB1784 + difference 3 1) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1784 + difference 1 3) (sourceB1784 + difference 3 1) sourceC1784) = raw21838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw21838; decide +kernel
    rw [ha]
    exact (canonical21838 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1784 + difference 1 4) (sourceB1784 + difference 4 1) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1784 + difference 1 4) (sourceB1784 + difference 4 1) sourceC1784) = raw25928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25928; decide +kernel
    rw [ha]
    exact (canonical25928 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1784 + difference 1 5) (sourceB1784 + difference 5 1) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4494) := by
    have ha : (tripleCharges (sourceA1784 + difference 1 5) (sourceB1784 + difference 5 1) sourceC1784) = raw25929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25929; decide +kernel
    rw [ha]
    exact (canonical25929 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1784 + difference 2 0) (sourceB1784 + difference 0 2) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4170) := by
    have ha : (tripleCharges (sourceA1784 + difference 2 0) (sourceB1784 + difference 0 2) sourceC1784) = raw25930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25930; decide +kernel
    rw [ha]
    exact (canonical25930 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1784 + difference 2 1) (sourceB1784 + difference 1 2) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4340) := by
    have ha : (tripleCharges (sourceA1784 + difference 2 1) (sourceB1784 + difference 1 2) sourceC1784) = raw25931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25931; decide +kernel
    rw [ha]
    exact (canonical25931 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1784 + difference 2 3) (sourceB1784 + difference 3 2) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1784 + difference 2 3) (sourceB1784 + difference 3 2) sourceC1784) = raw21842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw21842; decide +kernel
    rw [ha]
    exact (canonical21842 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1784 + difference 2 4) (sourceB1784 + difference 4 2) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1784 + difference 2 4) (sourceB1784 + difference 4 2) sourceC1784) = raw25932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25932; decide +kernel
    rw [ha]
    exact (canonical25932 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1784 + difference 2 5) (sourceB1784 + difference 5 2) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4494) := by
    have ha : (tripleCharges (sourceA1784 + difference 2 5) (sourceB1784 + difference 5 2) sourceC1784) = raw25933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25933; decide +kernel
    rw [ha]
    exact (canonical25933 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1784 + difference 3 0) (sourceB1784 + difference 0 3) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4179) := by
    have ha : (tripleCharges (sourceA1784 + difference 3 0) (sourceB1784 + difference 0 3) sourceC1784) = raw25934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25934; decide +kernel
    rw [ha]
    exact (canonical25934 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1784 + difference 3 1) (sourceB1784 + difference 1 3) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1784 + difference 3 1) (sourceB1784 + difference 1 3) sourceC1784) = raw25935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25935; decide +kernel
    rw [ha]
    exact (canonical25935 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1784 + difference 3 2) (sourceB1784 + difference 2 3) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1784 + difference 3 2) (sourceB1784 + difference 2 3) sourceC1784) = raw25936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25936; decide +kernel
    rw [ha]
    exact (canonical25936 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1784 + difference 3 4) (sourceB1784 + difference 4 3) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1784 + difference 3 4) (sourceB1784 + difference 4 3) sourceC1784) = raw25937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25937; decide +kernel
    rw [ha]
    exact (canonical25937 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1784 + difference 3 5) (sourceB1784 + difference 5 3) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA1784 + difference 3 5) (sourceB1784 + difference 5 3) sourceC1784) = raw25938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25938; decide +kernel
    rw [ha]
    exact (canonical25938 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1784 + difference 4 0) (sourceB1784 + difference 0 4) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4179) := by
    have ha : (tripleCharges (sourceA1784 + difference 4 0) (sourceB1784 + difference 0 4) sourceC1784) = raw25939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25939; decide +kernel
    rw [ha]
    exact (canonical25939 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1784 + difference 4 1) (sourceB1784 + difference 1 4) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1784 + difference 4 1) (sourceB1784 + difference 1 4) sourceC1784) = raw25940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25940; decide +kernel
    rw [ha]
    exact (canonical25940 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1784 + difference 4 2) (sourceB1784 + difference 2 4) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1784 + difference 4 2) (sourceB1784 + difference 2 4) sourceC1784) = raw25941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25941; decide +kernel
    rw [ha]
    exact (canonical25941 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1784 + difference 4 3) (sourceB1784 + difference 3 4) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1784 + difference 4 3) (sourceB1784 + difference 3 4) sourceC1784) = raw21851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw21851; decide +kernel
    rw [ha]
    exact (canonical21851 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1784 + difference 4 5) (sourceB1784 + difference 5 4) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA1784 + difference 4 5) (sourceB1784 + difference 5 4) sourceC1784) = raw25942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw25942; decide +kernel
    rw [ha]
    exact (canonical25942 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1784 + difference 5 0) (sourceB1784 + difference 0 5) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4174) := by
    have ha : (tripleCharges (sourceA1784 + difference 5 0) (sourceB1784 + difference 0 5) sourceC1784) = raw21843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw21843; decide +kernel
    rw [ha]
    exact (canonical21843 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1784 + difference 5 1) (sourceB1784 + difference 1 5) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1784 + difference 5 1) (sourceB1784 + difference 1 5) sourceC1784) = raw21844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw21844; decide +kernel
    rw [ha]
    exact (canonical21844 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1784 + difference 5 2) (sourceB1784 + difference 2 5) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1784 + difference 5 2) (sourceB1784 + difference 2 5) sourceC1784) = raw21845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw21845; decide +kernel
    rw [ha]
    exact (canonical21845 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1784 + difference 5 3) (sourceB1784 + difference 3 5) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1784 + difference 5 3) (sourceB1784 + difference 3 5) sourceC1784) = raw19911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw19911; decide +kernel
    rw [ha]
    exact (canonical19911 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1784 + difference 5 4) (sourceB1784 + difference 4 5) sourceC1784) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1784 + difference 5 4) (sourceB1784 + difference 4 5) sourceC1784) = raw19906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1784 sourceB1784 sourceC1784 difference raw19906; decide +kernel
    rw [ha]
    exact (canonical19906 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1784 sourceB1784 sourceC1784
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1784, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1785 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1785 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1785 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1785 : Integer.Sparse Master := [(Sum.inr 651, 2), (Sum.inr 652, 1), (Sum.inr 653, 2), (Sum.inr 1345, 2), (Sum.inr 1346, 2), (Sum.inr 1347, 4), (Sum.inr 1435, 2), (Sum.inr 1436, 2), (Sum.inr 1451, 4), (Sum.inr 1452, 2), (Sum.inr 1454, 2), (Sum.inr 2755, 1), (Sum.inr 3082, 2), (Sum.inr 3114, 2)]

theorem sourceEq1785 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1785 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1785 + difference 0 1) (sourceB1785 + difference 1 0) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA1785 + difference 0 1) (sourceB1785 + difference 1 0) sourceC1785) = raw25943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25943; decide +kernel
    rw [ha]
    exact (canonical25943 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1785 + difference 0 2) (sourceB1785 + difference 2 0) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA1785 + difference 0 2) (sourceB1785 + difference 2 0) sourceC1785) = raw25944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25944; decide +kernel
    rw [ha]
    exact (canonical25944 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1785 + difference 0 3) (sourceB1785 + difference 3 0) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA1785 + difference 0 3) (sourceB1785 + difference 3 0) sourceC1785) = raw25945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25945; decide +kernel
    rw [ha]
    exact (canonical25945 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1785 + difference 0 4) (sourceB1785 + difference 4 0) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA1785 + difference 0 4) (sourceB1785 + difference 4 0) sourceC1785) = raw25946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25946; decide +kernel
    rw [ha]
    exact (canonical25946 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1785 + difference 0 5) (sourceB1785 + difference 5 0) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA1785 + difference 0 5) (sourceB1785 + difference 5 0) sourceC1785) = raw25947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25947; decide +kernel
    rw [ha]
    exact (canonical25947 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1785 + difference 1 0) (sourceB1785 + difference 0 1) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 651) := by
    have ha : (tripleCharges (sourceA1785 + difference 1 0) (sourceB1785 + difference 0 1) sourceC1785) = raw25948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25948; decide +kernel
    rw [ha]
    exact (canonical25948 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1785 + difference 1 2) (sourceB1785 + difference 2 1) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1345) := by
    have ha : (tripleCharges (sourceA1785 + difference 1 2) (sourceB1785 + difference 2 1) sourceC1785) = raw25949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25949; decide +kernel
    rw [ha]
    exact (canonical25949 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1785 + difference 1 3) (sourceB1785 + difference 3 1) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1451) := by
    have ha : (tripleCharges (sourceA1785 + difference 1 3) (sourceB1785 + difference 3 1) sourceC1785) = raw25950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25950; decide +kernel
    rw [ha]
    exact (canonical25950 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1785 + difference 1 4) (sourceB1785 + difference 4 1) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1451) := by
    have ha : (tripleCharges (sourceA1785 + difference 1 4) (sourceB1785 + difference 4 1) sourceC1785) = raw25951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25951; decide +kernel
    rw [ha]
    exact (canonical25951 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1785 + difference 1 5) (sourceB1785 + difference 5 1) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1435) := by
    have ha : (tripleCharges (sourceA1785 + difference 1 5) (sourceB1785 + difference 5 1) sourceC1785) = raw25952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25952; decide +kernel
    rw [ha]
    exact (canonical25952 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1785 + difference 2 0) (sourceB1785 + difference 0 2) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 651) := by
    have ha : (tripleCharges (sourceA1785 + difference 2 0) (sourceB1785 + difference 0 2) sourceC1785) = raw25953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25953; decide +kernel
    rw [ha]
    exact (canonical25953 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1785 + difference 2 1) (sourceB1785 + difference 1 2) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1345) := by
    have ha : (tripleCharges (sourceA1785 + difference 2 1) (sourceB1785 + difference 1 2) sourceC1785) = raw25954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25954; decide +kernel
    rw [ha]
    exact (canonical25954 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1785 + difference 2 3) (sourceB1785 + difference 3 2) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1451) := by
    have ha : (tripleCharges (sourceA1785 + difference 2 3) (sourceB1785 + difference 3 2) sourceC1785) = raw25955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25955; decide +kernel
    rw [ha]
    exact (canonical25955 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1785 + difference 2 4) (sourceB1785 + difference 4 2) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1451) := by
    have ha : (tripleCharges (sourceA1785 + difference 2 4) (sourceB1785 + difference 4 2) sourceC1785) = raw25956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25956; decide +kernel
    rw [ha]
    exact (canonical25956 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1785 + difference 2 5) (sourceB1785 + difference 5 2) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1435) := by
    have ha : (tripleCharges (sourceA1785 + difference 2 5) (sourceB1785 + difference 5 2) sourceC1785) = raw25957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25957; decide +kernel
    rw [ha]
    exact (canonical25957 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1785 + difference 3 0) (sourceB1785 + difference 0 3) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 653) := by
    have ha : (tripleCharges (sourceA1785 + difference 3 0) (sourceB1785 + difference 0 3) sourceC1785) = raw25958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25958; decide +kernel
    rw [ha]
    exact (canonical25958 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1785 + difference 3 1) (sourceB1785 + difference 1 3) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1785 + difference 3 1) (sourceB1785 + difference 1 3) sourceC1785) = raw25959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25959; decide +kernel
    rw [ha]
    exact (canonical25959 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1785 + difference 3 2) (sourceB1785 + difference 2 3) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1785 + difference 3 2) (sourceB1785 + difference 2 3) sourceC1785) = raw25960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25960; decide +kernel
    rw [ha]
    exact (canonical25960 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1785 + difference 3 4) (sourceB1785 + difference 4 3) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1454) := by
    have ha : (tripleCharges (sourceA1785 + difference 3 4) (sourceB1785 + difference 4 3) sourceC1785) = raw25961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25961; decide +kernel
    rw [ha]
    exact (canonical25961 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1785 + difference 3 5) (sourceB1785 + difference 5 3) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA1785 + difference 3 5) (sourceB1785 + difference 5 3) sourceC1785) = raw25962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25962; decide +kernel
    rw [ha]
    exact (canonical25962 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1785 + difference 4 0) (sourceB1785 + difference 0 4) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 653) := by
    have ha : (tripleCharges (sourceA1785 + difference 4 0) (sourceB1785 + difference 0 4) sourceC1785) = raw25963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25963; decide +kernel
    rw [ha]
    exact (canonical25963 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1785 + difference 4 1) (sourceB1785 + difference 1 4) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1785 + difference 4 1) (sourceB1785 + difference 1 4) sourceC1785) = raw25964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25964; decide +kernel
    rw [ha]
    exact (canonical25964 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1785 + difference 4 2) (sourceB1785 + difference 2 4) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1785 + difference 4 2) (sourceB1785 + difference 2 4) sourceC1785) = raw25965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25965; decide +kernel
    rw [ha]
    exact (canonical25965 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1785 + difference 4 3) (sourceB1785 + difference 3 4) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1454) := by
    have ha : (tripleCharges (sourceA1785 + difference 4 3) (sourceB1785 + difference 3 4) sourceC1785) = raw25966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25966; decide +kernel
    rw [ha]
    exact (canonical25966 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1785 + difference 4 5) (sourceB1785 + difference 5 4) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA1785 + difference 4 5) (sourceB1785 + difference 5 4) sourceC1785) = raw25967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25967; decide +kernel
    rw [ha]
    exact (canonical25967 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1785 + difference 5 0) (sourceB1785 + difference 0 5) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 652) := by
    have ha : (tripleCharges (sourceA1785 + difference 5 0) (sourceB1785 + difference 0 5) sourceC1785) = raw25968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25968; decide +kernel
    rw [ha]
    exact (canonical25968 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1785 + difference 5 1) (sourceB1785 + difference 1 5) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1346) := by
    have ha : (tripleCharges (sourceA1785 + difference 5 1) (sourceB1785 + difference 1 5) sourceC1785) = raw25969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25969; decide +kernel
    rw [ha]
    exact (canonical25969 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1785 + difference 5 2) (sourceB1785 + difference 2 5) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1346) := by
    have ha : (tripleCharges (sourceA1785 + difference 5 2) (sourceB1785 + difference 2 5) sourceC1785) = raw25970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25970; decide +kernel
    rw [ha]
    exact (canonical25970 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1785 + difference 5 3) (sourceB1785 + difference 3 5) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1452) := by
    have ha : (tripleCharges (sourceA1785 + difference 5 3) (sourceB1785 + difference 3 5) sourceC1785) = raw25971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25971; decide +kernel
    rw [ha]
    exact (canonical25971 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1785 + difference 5 4) (sourceB1785 + difference 4 5) sourceC1785) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1452) := by
    have ha : (tripleCharges (sourceA1785 + difference 5 4) (sourceB1785 + difference 4 5) sourceC1785) = raw25972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1785 sourceB1785 sourceC1785 difference raw25972; decide +kernel
    rw [ha]
    exact (canonical25972 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1785 sourceB1785 sourceC1785
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1785, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1786 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1786 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1786 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1786 : Integer.Sparse Master := [(Sum.inr 1503, 2), (Sum.inr 1509, 1), (Sum.inr 1513, 2), (Sum.inr 1662, 2), (Sum.inr 1666, 2), (Sum.inr 1669, 4), (Sum.inr 1700, 2), (Sum.inr 1710, 4), (Sum.inr 1716, 2), (Sum.inr 1730, 2), (Sum.inr 1741, 2), (Sum.inr 2193, 2), (Sum.inr 2247, 1), (Sum.inr 2268, 2)]

theorem sourceEq1786 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1786 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1786 + difference 0 1) (sourceB1786 + difference 1 0) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1786 + difference 0 1) (sourceB1786 + difference 1 0) sourceC1786) = raw25973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25973; decide +kernel
    rw [ha]
    exact (canonical25973 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1786 + difference 0 2) (sourceB1786 + difference 2 0) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1786 + difference 0 2) (sourceB1786 + difference 2 0) sourceC1786) = raw25974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25974; decide +kernel
    rw [ha]
    exact (canonical25974 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1786 + difference 0 3) (sourceB1786 + difference 3 0) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA1786 + difference 0 3) (sourceB1786 + difference 3 0) sourceC1786) = raw21856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21856; decide +kernel
    rw [ha]
    exact (canonical21856 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1786 + difference 0 4) (sourceB1786 + difference 4 0) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA1786 + difference 0 4) (sourceB1786 + difference 4 0) sourceC1786) = raw25975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25975; decide +kernel
    rw [ha]
    exact (canonical25975 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1786 + difference 0 5) (sourceB1786 + difference 5 0) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA1786 + difference 0 5) (sourceB1786 + difference 5 0) sourceC1786) = raw25976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25976; decide +kernel
    rw [ha]
    exact (canonical25976 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1786 + difference 1 0) (sourceB1786 + difference 0 1) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1503) := by
    have ha : (tripleCharges (sourceA1786 + difference 1 0) (sourceB1786 + difference 0 1) sourceC1786) = raw25977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25977; decide +kernel
    rw [ha]
    exact (canonical25977 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1786 + difference 1 2) (sourceB1786 + difference 2 1) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1662) := by
    have ha : (tripleCharges (sourceA1786 + difference 1 2) (sourceB1786 + difference 2 1) sourceC1786) = raw25978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25978; decide +kernel
    rw [ha]
    exact (canonical25978 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1786 + difference 1 3) (sourceB1786 + difference 3 1) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1786 + difference 1 3) (sourceB1786 + difference 3 1) sourceC1786) = raw21860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21860; decide +kernel
    rw [ha]
    exact (canonical21860 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1786 + difference 1 4) (sourceB1786 + difference 4 1) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1786 + difference 1 4) (sourceB1786 + difference 4 1) sourceC1786) = raw25979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25979; decide +kernel
    rw [ha]
    exact (canonical25979 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1786 + difference 1 5) (sourceB1786 + difference 5 1) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA1786 + difference 1 5) (sourceB1786 + difference 5 1) sourceC1786) = raw25980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25980; decide +kernel
    rw [ha]
    exact (canonical25980 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1786 + difference 2 0) (sourceB1786 + difference 0 2) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1503) := by
    have ha : (tripleCharges (sourceA1786 + difference 2 0) (sourceB1786 + difference 0 2) sourceC1786) = raw25981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25981; decide +kernel
    rw [ha]
    exact (canonical25981 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1786 + difference 2 1) (sourceB1786 + difference 1 2) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1662) := by
    have ha : (tripleCharges (sourceA1786 + difference 2 1) (sourceB1786 + difference 1 2) sourceC1786) = raw25982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25982; decide +kernel
    rw [ha]
    exact (canonical25982 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1786 + difference 2 3) (sourceB1786 + difference 3 2) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1786 + difference 2 3) (sourceB1786 + difference 3 2) sourceC1786) = raw21864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21864; decide +kernel
    rw [ha]
    exact (canonical21864 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1786 + difference 2 4) (sourceB1786 + difference 4 2) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1786 + difference 2 4) (sourceB1786 + difference 4 2) sourceC1786) = raw25983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25983; decide +kernel
    rw [ha]
    exact (canonical25983 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1786 + difference 2 5) (sourceB1786 + difference 5 2) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA1786 + difference 2 5) (sourceB1786 + difference 5 2) sourceC1786) = raw25984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25984; decide +kernel
    rw [ha]
    exact (canonical25984 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1786 + difference 3 0) (sourceB1786 + difference 0 3) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1786 + difference 3 0) (sourceB1786 + difference 0 3) sourceC1786) = raw25985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25985; decide +kernel
    rw [ha]
    exact (canonical25985 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1786 + difference 3 1) (sourceB1786 + difference 1 3) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1786 + difference 3 1) (sourceB1786 + difference 1 3) sourceC1786) = raw25986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25986; decide +kernel
    rw [ha]
    exact (canonical25986 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1786 + difference 3 2) (sourceB1786 + difference 2 3) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1786 + difference 3 2) (sourceB1786 + difference 2 3) sourceC1786) = raw25987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25987; decide +kernel
    rw [ha]
    exact (canonical25987 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1786 + difference 3 4) (sourceB1786 + difference 4 3) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1786 + difference 3 4) (sourceB1786 + difference 4 3) sourceC1786) = raw25988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25988; decide +kernel
    rw [ha]
    exact (canonical25988 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1786 + difference 3 5) (sourceB1786 + difference 5 3) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1786 + difference 3 5) (sourceB1786 + difference 5 3) sourceC1786) = raw25989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25989; decide +kernel
    rw [ha]
    exact (canonical25989 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1786 + difference 4 0) (sourceB1786 + difference 0 4) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1786 + difference 4 0) (sourceB1786 + difference 0 4) sourceC1786) = raw25990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25990; decide +kernel
    rw [ha]
    exact (canonical25990 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1786 + difference 4 1) (sourceB1786 + difference 1 4) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1786 + difference 4 1) (sourceB1786 + difference 1 4) sourceC1786) = raw25991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25991; decide +kernel
    rw [ha]
    exact (canonical25991 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1786 + difference 4 2) (sourceB1786 + difference 2 4) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1786 + difference 4 2) (sourceB1786 + difference 2 4) sourceC1786) = raw25992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25992; decide +kernel
    rw [ha]
    exact (canonical25992 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1786 + difference 4 3) (sourceB1786 + difference 3 4) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1786 + difference 4 3) (sourceB1786 + difference 3 4) sourceC1786) = raw21873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21873; decide +kernel
    rw [ha]
    exact (canonical21873 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1786 + difference 4 5) (sourceB1786 + difference 5 4) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1786 + difference 4 5) (sourceB1786 + difference 5 4) sourceC1786) = raw25993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw25993; decide +kernel
    rw [ha]
    exact (canonical25993 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1786 + difference 5 0) (sourceB1786 + difference 0 5) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA1786 + difference 5 0) (sourceB1786 + difference 0 5) sourceC1786) = raw21865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21865; decide +kernel
    rw [ha]
    exact (canonical21865 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1786 + difference 5 1) (sourceB1786 + difference 1 5) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1786 + difference 5 1) (sourceB1786 + difference 1 5) sourceC1786) = raw21866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21866; decide +kernel
    rw [ha]
    exact (canonical21866 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1786 + difference 5 2) (sourceB1786 + difference 2 5) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1786 + difference 5 2) (sourceB1786 + difference 2 5) sourceC1786) = raw21867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw21867; decide +kernel
    rw [ha]
    exact (canonical21867 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1786 + difference 5 3) (sourceB1786 + difference 3 5) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1786 + difference 5 3) (sourceB1786 + difference 3 5) sourceC1786) = raw19941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw19941; decide +kernel
    rw [ha]
    exact (canonical19941 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1786 + difference 5 4) (sourceB1786 + difference 4 5) sourceC1786) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1786 + difference 5 4) (sourceB1786 + difference 4 5) sourceC1786) = raw19936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1786 sourceB1786 sourceC1786 difference raw19936; decide +kernel
    rw [ha]
    exact (canonical19936 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1786 sourceB1786 sourceC1786
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1786, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1787 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1787 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1787 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1787 : Integer.Sparse Master := [(Sum.inr 598, 2), (Sum.inr 602, 1), (Sum.inr 607, 2), (Sum.inr 1080, 1), (Sum.inr 4085, -1)]

theorem sourceEq1787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1787 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1787 + difference 0 0) (sourceB1787 + difference 0 0) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1787 + difference 0 0) (sourceB1787 + difference 0 0) sourceC1787) = raw25994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw25994; decide +kernel
    rw [ha]
    exact (canonical25994 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1787 + difference 1 0) (sourceB1787 + difference 0 1) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 598) := by
    have ha : (tripleCharges (sourceA1787 + difference 1 0) (sourceB1787 + difference 0 1) sourceC1787) = raw25995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw25995; decide +kernel
    rw [ha]
    exact (canonical25995 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1787 + difference 2 0) (sourceB1787 + difference 0 2) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 598) := by
    have ha : (tripleCharges (sourceA1787 + difference 2 0) (sourceB1787 + difference 0 2) sourceC1787) = raw25996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw25996; decide +kernel
    rw [ha]
    exact (canonical25996 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1787 + difference 3 0) (sourceB1787 + difference 0 3) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1787 + difference 3 0) (sourceB1787 + difference 0 3) sourceC1787) = raw25997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw25997; decide +kernel
    rw [ha]
    exact (canonical25997 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1787 + difference 4 0) (sourceB1787 + difference 0 4) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1787 + difference 4 0) (sourceB1787 + difference 0 4) sourceC1787) = raw25998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw25998; decide +kernel
    rw [ha]
    exact (canonical25998 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1787 + difference 5 0) (sourceB1787 + difference 0 5) sourceC1787) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1787 + difference 5 0) (sourceB1787 + difference 0 5) sourceC1787) = raw21878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1787 sourceB1787 sourceC1787 difference raw21878; decide +kernel
    rw [ha]
    exact (canonical21878 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1787 + sourceB1787) sourceC1787) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1787 + sourceB1787) sourceC1787) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA1787 sourceB1787 sourceC1787 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1787 sourceB1787 sourceC1787
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1787, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1788 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1788 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1788 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1788 : Integer.Sparse Master := [(Sum.inr 598, 1), (Sum.inr 918, 1), (Sum.inr 1078, 1), (Sum.inr 1080, 3), (Sum.inr 4085, -1)]

theorem sourceEq1788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1788 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 0) (sourceB1788 + difference 0 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 598) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 0) (sourceB1788 + difference 0 1) sourceC1788) = raw25995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw25995; decide +kernel
    rw [ha]
    exact (canonical25995 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 1) (sourceB1788 + difference 1 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 1) (sourceB1788 + difference 1 1) sourceC1788) = raw25994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw25994; decide +kernel
    rw [ha]
    exact (canonical25994 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 2) (sourceB1788 + difference 2 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 918) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 2) (sourceB1788 + difference 2 1) sourceC1788) = raw25999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw25999; decide +kernel
    rw [ha]
    exact (canonical25999 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 3) (sourceB1788 + difference 3 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 3) (sourceB1788 + difference 3 1) sourceC1788) = raw21883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw21883; decide +kernel
    rw [ha]
    exact (canonical21883 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 4) (sourceB1788 + difference 4 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 4) (sourceB1788 + difference 4 1) sourceC1788) = raw26000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw26000; decide +kernel
    rw [ha]
    exact (canonical26000 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1788 + difference 1 5) (sourceB1788 + difference 5 1) sourceC1788) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1078) := by
    have ha : (tripleCharges (sourceA1788 + difference 1 5) (sourceB1788 + difference 5 1) sourceC1788) = raw26001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1788 sourceB1788 sourceC1788 difference raw26001; decide +kernel
    rw [ha]
    exact (canonical26001 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1788 + sourceB1788) sourceC1788) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1788 + sourceB1788) sourceC1788) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA1788 sourceB1788 sourceC1788 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1788 sourceB1788 sourceC1788
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1788, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1789 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1789 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1789 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceForm1789 : Integer.Sparse Master := [(Sum.inr 4114, 2), (Sum.inr 4116, 1), (Sum.inr 4122, 2), (Sum.inr 4297, 2), (Sum.inr 4299, 2), (Sum.inr 4304, 4), (Sum.inr 4418, 4), (Sum.inr 4421, 2), (Sum.inr 4431, 2), (Sum.inr 4495, 2), (Sum.inr 4499, 2), (Sum.inr 5099, 2), (Sum.inr 5272, 2), (Sum.inr 5306, 1)]

theorem sourceEq1789 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1789 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1789 + difference 0 1) (sourceB1789 + difference 1 0) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA1789 + difference 0 1) (sourceB1789 + difference 1 0) sourceC1789) = raw10688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw10688; decide +kernel
    rw [ha]
    exact (canonical10688 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1789 + difference 0 2) (sourceB1789 + difference 2 0) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA1789 + difference 0 2) (sourceB1789 + difference 2 0) sourceC1789) = raw10689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw10689; decide +kernel
    rw [ha]
    exact (canonical10689 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1789 + difference 0 3) (sourceB1789 + difference 3 0) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA1789 + difference 0 3) (sourceB1789 + difference 3 0) sourceC1789) = raw12152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw12152; decide +kernel
    rw [ha]
    exact (canonical12152 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1789 + difference 0 4) (sourceB1789 + difference 4 0) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA1789 + difference 0 4) (sourceB1789 + difference 4 0) sourceC1789) = raw10690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw10690; decide +kernel
    rw [ha]
    exact (canonical10690 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1789 + difference 0 5) (sourceB1789 + difference 5 0) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA1789 + difference 0 5) (sourceB1789 + difference 5 0) sourceC1789) = raw10691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw10691; decide +kernel
    rw [ha]
    exact (canonical10691 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1789 + difference 1 0) (sourceB1789 + difference 0 1) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4114) := by
    have ha : (tripleCharges (sourceA1789 + difference 1 0) (sourceB1789 + difference 0 1) sourceC1789) = raw26002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26002; decide +kernel
    rw [ha]
    exact (canonical26002 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1789 + difference 1 2) (sourceB1789 + difference 2 1) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4297) := by
    have ha : (tripleCharges (sourceA1789 + difference 1 2) (sourceB1789 + difference 2 1) sourceC1789) = raw26003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26003; decide +kernel
    rw [ha]
    exact (canonical26003 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1789 + difference 1 3) (sourceB1789 + difference 3 1) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1789 + difference 1 3) (sourceB1789 + difference 3 1) sourceC1789) = raw10677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw10677; decide +kernel
    rw [ha]
    exact (canonical10677 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1789 + difference 1 4) (sourceB1789 + difference 4 1) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1789 + difference 1 4) (sourceB1789 + difference 4 1) sourceC1789) = raw26004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26004; decide +kernel
    rw [ha]
    exact (canonical26004 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1789 + difference 1 5) (sourceB1789 + difference 5 1) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1789 + difference 1 5) (sourceB1789 + difference 5 1) sourceC1789) = raw12135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw12135; decide +kernel
    rw [ha]
    exact (canonical12135 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1789 + difference 2 0) (sourceB1789 + difference 0 2) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4114) := by
    have ha : (tripleCharges (sourceA1789 + difference 2 0) (sourceB1789 + difference 0 2) sourceC1789) = raw26005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26005; decide +kernel
    rw [ha]
    exact (canonical26005 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1789 + difference 2 1) (sourceB1789 + difference 1 2) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4297) := by
    have ha : (tripleCharges (sourceA1789 + difference 2 1) (sourceB1789 + difference 1 2) sourceC1789) = raw26006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26006; decide +kernel
    rw [ha]
    exact (canonical26006 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1789 + difference 2 3) (sourceB1789 + difference 3 2) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1789 + difference 2 3) (sourceB1789 + difference 3 2) sourceC1789) = raw10682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw10682; decide +kernel
    rw [ha]
    exact (canonical10682 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1789 + difference 2 4) (sourceB1789 + difference 4 2) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1789 + difference 2 4) (sourceB1789 + difference 4 2) sourceC1789) = raw26007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26007; decide +kernel
    rw [ha]
    exact (canonical26007 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1789 + difference 2 5) (sourceB1789 + difference 5 2) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1789 + difference 2 5) (sourceB1789 + difference 5 2) sourceC1789) = raw12139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw12139; decide +kernel
    rw [ha]
    exact (canonical12139 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1789 + difference 3 0) (sourceB1789 + difference 0 3) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4122) := by
    have ha : (tripleCharges (sourceA1789 + difference 3 0) (sourceB1789 + difference 0 3) sourceC1789) = raw26008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26008; decide +kernel
    rw [ha]
    exact (canonical26008 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1789 + difference 3 1) (sourceB1789 + difference 1 3) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA1789 + difference 3 1) (sourceB1789 + difference 1 3) sourceC1789) = raw26009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26009; decide +kernel
    rw [ha]
    exact (canonical26009 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1789 + difference 3 2) (sourceB1789 + difference 2 3) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA1789 + difference 3 2) (sourceB1789 + difference 2 3) sourceC1789) = raw26010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26010; decide +kernel
    rw [ha]
    exact (canonical26010 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1789 + difference 3 4) (sourceB1789 + difference 4 3) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1789 + difference 3 4) (sourceB1789 + difference 4 3) sourceC1789) = raw26011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26011; decide +kernel
    rw [ha]
    exact (canonical26011 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1789 + difference 3 5) (sourceB1789 + difference 5 3) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1789 + difference 3 5) (sourceB1789 + difference 5 3) sourceC1789) = raw12143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw12143; decide +kernel
    rw [ha]
    exact (canonical12143 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1789 + difference 4 0) (sourceB1789 + difference 0 4) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4122) := by
    have ha : (tripleCharges (sourceA1789 + difference 4 0) (sourceB1789 + difference 0 4) sourceC1789) = raw26012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26012; decide +kernel
    rw [ha]
    exact (canonical26012 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1789 + difference 4 1) (sourceB1789 + difference 1 4) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA1789 + difference 4 1) (sourceB1789 + difference 1 4) sourceC1789) = raw26013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26013; decide +kernel
    rw [ha]
    exact (canonical26013 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1789 + difference 4 2) (sourceB1789 + difference 2 4) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA1789 + difference 4 2) (sourceB1789 + difference 2 4) sourceC1789) = raw26014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26014; decide +kernel
    rw [ha]
    exact (canonical26014 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1789 + difference 4 3) (sourceB1789 + difference 3 4) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1789 + difference 4 3) (sourceB1789 + difference 3 4) sourceC1789) = raw10692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw10692; decide +kernel
    rw [ha]
    exact (canonical10692 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1789 + difference 4 5) (sourceB1789 + difference 5 4) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1789 + difference 4 5) (sourceB1789 + difference 5 4) sourceC1789) = raw12148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw12148; decide +kernel
    rw [ha]
    exact (canonical12148 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1789 + difference 5 0) (sourceB1789 + difference 0 5) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4116) := by
    have ha : (tripleCharges (sourceA1789 + difference 5 0) (sourceB1789 + difference 0 5) sourceC1789) = raw26015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26015; decide +kernel
    rw [ha]
    exact (canonical26015 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1789 + difference 5 1) (sourceB1789 + difference 1 5) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4299) := by
    have ha : (tripleCharges (sourceA1789 + difference 5 1) (sourceB1789 + difference 1 5) sourceC1789) = raw26016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26016; decide +kernel
    rw [ha]
    exact (canonical26016 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1789 + difference 5 2) (sourceB1789 + difference 2 5) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4299) := by
    have ha : (tripleCharges (sourceA1789 + difference 5 2) (sourceB1789 + difference 2 5) sourceC1789) = raw26017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26017; decide +kernel
    rw [ha]
    exact (canonical26017 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1789 + difference 5 3) (sourceB1789 + difference 3 5) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4421) := by
    have ha : (tripleCharges (sourceA1789 + difference 5 3) (sourceB1789 + difference 3 5) sourceC1789) = raw10697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw10697; decide +kernel
    rw [ha]
    exact (canonical10697 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1789 + difference 5 4) (sourceB1789 + difference 4 5) sourceC1789) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4421) := by
    have ha : (tripleCharges (sourceA1789 + difference 5 4) (sourceB1789 + difference 4 5) sourceC1789) = raw26018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1789 sourceB1789 sourceC1789 difference raw26018; decide +kernel
    rw [ha]
    exact (canonical26018 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1789 sourceB1789 sourceC1789
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1789, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1790 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1790 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1790 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceForm1790 : Integer.Sparse Master := [(Sum.inr 551, 2), (Sum.inr 553, 1), (Sum.inr 556, 2), (Sum.inr 875, 2), (Sum.inr 877, 2), (Sum.inr 882, 4), (Sum.inr 999, 4), (Sum.inr 1002, 2), (Sum.inr 1012, 2), (Sum.inr 1079, 2), (Sum.inr 1083, 2), (Sum.inr 2509, 2), (Sum.inr 2740, 2), (Sum.inr 2784, 1)]

theorem sourceEq1790 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1790 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1790 + difference 0 1) (sourceB1790 + difference 1 0) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA1790 + difference 0 1) (sourceB1790 + difference 1 0) sourceC1790) = raw12179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw12179; decide +kernel
    rw [ha]
    exact (canonical12179 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1790 + difference 0 2) (sourceB1790 + difference 2 0) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA1790 + difference 0 2) (sourceB1790 + difference 2 0) sourceC1790) = raw12180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw12180; decide +kernel
    rw [ha]
    exact (canonical12180 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1790 + difference 0 3) (sourceB1790 + difference 3 0) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA1790 + difference 0 3) (sourceB1790 + difference 3 0) sourceC1790) = raw12181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw12181; decide +kernel
    rw [ha]
    exact (canonical12181 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1790 + difference 0 4) (sourceB1790 + difference 4 0) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA1790 + difference 0 4) (sourceB1790 + difference 4 0) sourceC1790) = raw12182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw12182; decide +kernel
    rw [ha]
    exact (canonical12182 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1790 + difference 0 5) (sourceB1790 + difference 5 0) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA1790 + difference 0 5) (sourceB1790 + difference 5 0) sourceC1790) = raw26019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26019; decide +kernel
    rw [ha]
    exact (canonical26019 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1790 + difference 1 0) (sourceB1790 + difference 0 1) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 551) := by
    have ha : (tripleCharges (sourceA1790 + difference 1 0) (sourceB1790 + difference 0 1) sourceC1790) = raw26020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26020; decide +kernel
    rw [ha]
    exact (canonical26020 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1790 + difference 1 2) (sourceB1790 + difference 2 1) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 875) := by
    have ha : (tripleCharges (sourceA1790 + difference 1 2) (sourceB1790 + difference 2 1) sourceC1790) = raw26021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26021; decide +kernel
    rw [ha]
    exact (canonical26021 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1790 + difference 1 3) (sourceB1790 + difference 3 1) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1790 + difference 1 3) (sourceB1790 + difference 3 1) sourceC1790) = raw26022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26022; decide +kernel
    rw [ha]
    exact (canonical26022 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1790 + difference 1 4) (sourceB1790 + difference 4 1) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1790 + difference 1 4) (sourceB1790 + difference 4 1) sourceC1790) = raw26023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26023; decide +kernel
    rw [ha]
    exact (canonical26023 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1790 + difference 1 5) (sourceB1790 + difference 5 1) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1790 + difference 1 5) (sourceB1790 + difference 5 1) sourceC1790) = raw12158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw12158; decide +kernel
    rw [ha]
    exact (canonical12158 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1790 + difference 2 0) (sourceB1790 + difference 0 2) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 551) := by
    have ha : (tripleCharges (sourceA1790 + difference 2 0) (sourceB1790 + difference 0 2) sourceC1790) = raw26024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26024; decide +kernel
    rw [ha]
    exact (canonical26024 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1790 + difference 2 1) (sourceB1790 + difference 1 2) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 875) := by
    have ha : (tripleCharges (sourceA1790 + difference 2 1) (sourceB1790 + difference 1 2) sourceC1790) = raw26025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26025; decide +kernel
    rw [ha]
    exact (canonical26025 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1790 + difference 2 3) (sourceB1790 + difference 3 2) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1790 + difference 2 3) (sourceB1790 + difference 3 2) sourceC1790) = raw26026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26026; decide +kernel
    rw [ha]
    exact (canonical26026 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1790 + difference 2 4) (sourceB1790 + difference 4 2) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1790 + difference 2 4) (sourceB1790 + difference 4 2) sourceC1790) = raw26027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26027; decide +kernel
    rw [ha]
    exact (canonical26027 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1790 + difference 2 5) (sourceB1790 + difference 5 2) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1790 + difference 2 5) (sourceB1790 + difference 5 2) sourceC1790) = raw12163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw12163; decide +kernel
    rw [ha]
    exact (canonical12163 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1790 + difference 3 0) (sourceB1790 + difference 0 3) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 556) := by
    have ha : (tripleCharges (sourceA1790 + difference 3 0) (sourceB1790 + difference 0 3) sourceC1790) = raw26028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26028; decide +kernel
    rw [ha]
    exact (canonical26028 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1790 + difference 3 1) (sourceB1790 + difference 1 3) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA1790 + difference 3 1) (sourceB1790 + difference 1 3) sourceC1790) = raw26029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26029; decide +kernel
    rw [ha]
    exact (canonical26029 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1790 + difference 3 2) (sourceB1790 + difference 2 3) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA1790 + difference 3 2) (sourceB1790 + difference 2 3) sourceC1790) = raw26030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26030; decide +kernel
    rw [ha]
    exact (canonical26030 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1790 + difference 3 4) (sourceB1790 + difference 4 3) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1790 + difference 3 4) (sourceB1790 + difference 4 3) sourceC1790) = raw26031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26031; decide +kernel
    rw [ha]
    exact (canonical26031 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1790 + difference 3 5) (sourceB1790 + difference 5 3) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1790 + difference 3 5) (sourceB1790 + difference 5 3) sourceC1790) = raw12168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw12168; decide +kernel
    rw [ha]
    exact (canonical12168 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1790 + difference 4 0) (sourceB1790 + difference 0 4) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 556) := by
    have ha : (tripleCharges (sourceA1790 + difference 4 0) (sourceB1790 + difference 0 4) sourceC1790) = raw26032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26032; decide +kernel
    rw [ha]
    exact (canonical26032 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1790 + difference 4 1) (sourceB1790 + difference 1 4) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA1790 + difference 4 1) (sourceB1790 + difference 1 4) sourceC1790) = raw26033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26033; decide +kernel
    rw [ha]
    exact (canonical26033 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1790 + difference 4 2) (sourceB1790 + difference 2 4) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA1790 + difference 4 2) (sourceB1790 + difference 2 4) sourceC1790) = raw26034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26034; decide +kernel
    rw [ha]
    exact (canonical26034 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1790 + difference 4 3) (sourceB1790 + difference 3 4) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1790 + difference 4 3) (sourceB1790 + difference 3 4) sourceC1790) = raw26035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26035; decide +kernel
    rw [ha]
    exact (canonical26035 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1790 + difference 4 5) (sourceB1790 + difference 5 4) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1790 + difference 4 5) (sourceB1790 + difference 5 4) sourceC1790) = raw12173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw12173; decide +kernel
    rw [ha]
    exact (canonical12173 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1790 + difference 5 0) (sourceB1790 + difference 0 5) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 553) := by
    have ha : (tripleCharges (sourceA1790 + difference 5 0) (sourceB1790 + difference 0 5) sourceC1790) = raw26036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26036; decide +kernel
    rw [ha]
    exact (canonical26036 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1790 + difference 5 1) (sourceB1790 + difference 1 5) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 877) := by
    have ha : (tripleCharges (sourceA1790 + difference 5 1) (sourceB1790 + difference 1 5) sourceC1790) = raw26037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26037; decide +kernel
    rw [ha]
    exact (canonical26037 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1790 + difference 5 2) (sourceB1790 + difference 2 5) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 877) := by
    have ha : (tripleCharges (sourceA1790 + difference 5 2) (sourceB1790 + difference 2 5) sourceC1790) = raw26038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26038; decide +kernel
    rw [ha]
    exact (canonical26038 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1790 + difference 5 3) (sourceB1790 + difference 3 5) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1002) := by
    have ha : (tripleCharges (sourceA1790 + difference 5 3) (sourceB1790 + difference 3 5) sourceC1790) = raw26039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26039; decide +kernel
    rw [ha]
    exact (canonical26039 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1790 + difference 5 4) (sourceB1790 + difference 4 5) sourceC1790) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1002) := by
    have ha : (tripleCharges (sourceA1790 + difference 5 4) (sourceB1790 + difference 4 5) sourceC1790) = raw26040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1790 sourceB1790 sourceC1790 difference raw26040; decide +kernel
    rw [ha]
    exact (canonical26040 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1790 sourceB1790 sourceC1790
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1790, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1791 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB1791 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1791 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1791 : Integer.Sparse Master := [(Sum.inr 4251, 2), (Sum.inr 4257, 1), (Sum.inr 4269, 2), (Sum.inr 4395, 2), (Sum.inr 4416, 2), (Sum.inr 4418, 4), (Sum.inr 4450, 4), (Sum.inr 4457, 2), (Sum.inr 4488, 2), (Sum.inr 4490, 2), (Sum.inr 4498, 2), (Sum.inr 4600, 2), (Sum.inr 4617, 2), (Sum.inr 4623, 1)]

theorem sourceEq1791 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1791 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1791 + difference 0 1) (sourceB1791 + difference 1 0) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1791 + difference 0 1) (sourceB1791 + difference 1 0) sourceC1791) = raw24178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw24178; decide +kernel
    rw [ha]
    exact (canonical24178 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1791 + difference 0 2) (sourceB1791 + difference 2 0) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1791 + difference 0 2) (sourceB1791 + difference 2 0) sourceC1791) = raw24179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw24179; decide +kernel
    rw [ha]
    exact (canonical24179 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1791 + difference 0 3) (sourceB1791 + difference 3 0) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1791 + difference 0 3) (sourceB1791 + difference 3 0) sourceC1791) = raw24180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw24180; decide +kernel
    rw [ha]
    exact (canonical24180 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1791 + difference 0 4) (sourceB1791 + difference 4 0) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1791 + difference 0 4) (sourceB1791 + difference 4 0) sourceC1791) = raw24181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw24181; decide +kernel
    rw [ha]
    exact (canonical24181 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1791 + difference 0 5) (sourceB1791 + difference 5 0) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1791 + difference 0 5) (sourceB1791 + difference 5 0) sourceC1791) = raw24269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw24269; decide +kernel
    rw [ha]
    exact (canonical24269 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1791 + difference 1 0) (sourceB1791 + difference 0 1) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1791 + difference 1 0) (sourceB1791 + difference 0 1) sourceC1791) = raw25481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw25481; decide +kernel
    rw [ha]
    exact (canonical25481 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1791 + difference 1 2) (sourceB1791 + difference 2 1) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4395) := by
    have ha : (tripleCharges (sourceA1791 + difference 1 2) (sourceB1791 + difference 2 1) sourceC1791) = raw25482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw25482; decide +kernel
    rw [ha]
    exact (canonical25482 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1791 + difference 1 3) (sourceB1791 + difference 3 1) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4450) := by
    have ha : (tripleCharges (sourceA1791 + difference 1 3) (sourceB1791 + difference 3 1) sourceC1791) = raw25483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw25483; decide +kernel
    rw [ha]
    exact (canonical25483 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1791 + difference 1 4) (sourceB1791 + difference 4 1) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4450) := by
    have ha : (tripleCharges (sourceA1791 + difference 1 4) (sourceB1791 + difference 4 1) sourceC1791) = raw25484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw25484; decide +kernel
    rw [ha]
    exact (canonical25484 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1791 + difference 1 5) (sourceB1791 + difference 5 1) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1791 + difference 1 5) (sourceB1791 + difference 5 1) sourceC1791) = raw24157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw24157; decide +kernel
    rw [ha]
    exact (canonical24157 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1791 + difference 2 0) (sourceB1791 + difference 0 2) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1791 + difference 2 0) (sourceB1791 + difference 0 2) sourceC1791) = raw26041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26041; decide +kernel
    rw [ha]
    exact (canonical26041 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1791 + difference 2 1) (sourceB1791 + difference 1 2) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4395) := by
    have ha : (tripleCharges (sourceA1791 + difference 2 1) (sourceB1791 + difference 1 2) sourceC1791) = raw26042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26042; decide +kernel
    rw [ha]
    exact (canonical26042 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1791 + difference 2 3) (sourceB1791 + difference 3 2) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4450) := by
    have ha : (tripleCharges (sourceA1791 + difference 2 3) (sourceB1791 + difference 3 2) sourceC1791) = raw26043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26043; decide +kernel
    rw [ha]
    exact (canonical26043 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1791 + difference 2 4) (sourceB1791 + difference 4 2) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4450) := by
    have ha : (tripleCharges (sourceA1791 + difference 2 4) (sourceB1791 + difference 4 2) sourceC1791) = raw26044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26044; decide +kernel
    rw [ha]
    exact (canonical26044 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1791 + difference 2 5) (sourceB1791 + difference 5 2) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1791 + difference 2 5) (sourceB1791 + difference 5 2) sourceC1791) = raw24162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw24162; decide +kernel
    rw [ha]
    exact (canonical24162 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1791 + difference 3 0) (sourceB1791 + difference 0 3) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1791 + difference 3 0) (sourceB1791 + difference 0 3) sourceC1791) = raw26045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26045; decide +kernel
    rw [ha]
    exact (canonical26045 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1791 + difference 3 1) (sourceB1791 + difference 1 3) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1791 + difference 3 1) (sourceB1791 + difference 1 3) sourceC1791) = raw26046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26046; decide +kernel
    rw [ha]
    exact (canonical26046 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1791 + difference 3 2) (sourceB1791 + difference 2 3) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1791 + difference 3 2) (sourceB1791 + difference 2 3) sourceC1791) = raw24822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw24822; decide +kernel
    rw [ha]
    exact (canonical24822 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1791 + difference 3 4) (sourceB1791 + difference 4 3) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1791 + difference 3 4) (sourceB1791 + difference 4 3) sourceC1791) = raw26047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26047; decide +kernel
    rw [ha]
    exact (canonical26047 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1791 + difference 3 5) (sourceB1791 + difference 5 3) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1791 + difference 3 5) (sourceB1791 + difference 5 3) sourceC1791) = raw24167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw24167; decide +kernel
    rw [ha]
    exact (canonical24167 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1791 + difference 4 0) (sourceB1791 + difference 0 4) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1791 + difference 4 0) (sourceB1791 + difference 0 4) sourceC1791) = raw26048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26048; decide +kernel
    rw [ha]
    exact (canonical26048 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1791 + difference 4 1) (sourceB1791 + difference 1 4) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1791 + difference 4 1) (sourceB1791 + difference 1 4) sourceC1791) = raw26049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26049; decide +kernel
    rw [ha]
    exact (canonical26049 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1791 + difference 4 2) (sourceB1791 + difference 2 4) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1791 + difference 4 2) (sourceB1791 + difference 2 4) sourceC1791) = raw26050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26050; decide +kernel
    rw [ha]
    exact (canonical26050 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1791 + difference 4 3) (sourceB1791 + difference 3 4) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1791 + difference 4 3) (sourceB1791 + difference 3 4) sourceC1791) = raw26051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26051; decide +kernel
    rw [ha]
    exact (canonical26051 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1791 + difference 4 5) (sourceB1791 + difference 5 4) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1791 + difference 4 5) (sourceB1791 + difference 5 4) sourceC1791) = raw24172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw24172; decide +kernel
    rw [ha]
    exact (canonical24172 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1791 + difference 5 0) (sourceB1791 + difference 0 5) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA1791 + difference 5 0) (sourceB1791 + difference 0 5) sourceC1791) = raw26052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26052; decide +kernel
    rw [ha]
    exact (canonical26052 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1791 + difference 5 1) (sourceB1791 + difference 1 5) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4416) := by
    have ha : (tripleCharges (sourceA1791 + difference 5 1) (sourceB1791 + difference 1 5) sourceC1791) = raw26053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26053; decide +kernel
    rw [ha]
    exact (canonical26053 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1791 + difference 5 2) (sourceB1791 + difference 2 5) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4416) := by
    have ha : (tripleCharges (sourceA1791 + difference 5 2) (sourceB1791 + difference 2 5) sourceC1791) = raw26054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26054; decide +kernel
    rw [ha]
    exact (canonical26054 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1791 + difference 5 3) (sourceB1791 + difference 3 5) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4488) := by
    have ha : (tripleCharges (sourceA1791 + difference 5 3) (sourceB1791 + difference 3 5) sourceC1791) = raw26055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26055; decide +kernel
    rw [ha]
    exact (canonical26055 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1791 + difference 5 4) (sourceB1791 + difference 4 5) sourceC1791) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4488) := by
    have ha : (tripleCharges (sourceA1791 + difference 5 4) (sourceB1791 + difference 4 5) sourceC1791) = raw26056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1791 sourceB1791 sourceC1791 difference raw26056; decide +kernel
    rw [ha]
    exact (canonical26056 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1791 sourceB1791 sourceC1791
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1791, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
