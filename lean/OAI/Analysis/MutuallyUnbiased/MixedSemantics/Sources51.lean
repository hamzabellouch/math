import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical187
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical190

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1632 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceB1632 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1632 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1632 : Integer.Sparse Master := [(Sum.inr 1607, 2), (Sum.inr 1609, 1), (Sum.inr 1616, 1), (Sum.inr 1737, 1), (Sum.inr 3288, 1), (Sum.inr 4069, -1)]

theorem sourceEq1632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1632 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 0) (sourceB1632 + difference 0 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 0) (sourceB1632 + difference 0 0) sourceC1632) = raw23953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw23953; decide +kernel
    rw [ha]
    exact (canonical23953 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 1) (sourceB1632 + difference 1 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1609) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 1) (sourceB1632 + difference 1 0) sourceC1632) = raw24028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw24028; decide +kernel
    rw [ha]
    exact (canonical24028 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 2) (sourceB1632 + difference 2 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 2) (sourceB1632 + difference 2 0) sourceC1632) = raw23942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw23942; decide +kernel
    rw [ha]
    exact (canonical23942 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 3) (sourceB1632 + difference 3 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 3) (sourceB1632 + difference 3 0) sourceC1632) = raw24029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw24029; decide +kernel
    rw [ha]
    exact (canonical24029 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 4) (sourceB1632 + difference 4 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 4) (sourceB1632 + difference 4 0) sourceC1632) = raw24030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw24030; decide +kernel
    rw [ha]
    exact (canonical24030 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 5) (sourceB1632 + difference 5 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1616) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 5) (sourceB1632 + difference 5 0) sourceC1632) = raw24031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw24031; decide +kernel
    rw [ha]
    exact (canonical24031 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1632 + sourceB1632) sourceC1632) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1632 + sourceB1632) sourceC1632) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1632 sourceB1632 sourceC1632 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1632 sourceB1632 sourceC1632
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1632, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1633 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceB1633 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1633 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1633 : Integer.Sparse Master := [(Sum.inr 1592, 1), (Sum.inr 1594, 1), (Sum.inr 1597, 2), (Sum.inr 1707, 1), (Sum.inr 3288, 1), (Sum.inr 4069, -1)]

theorem sourceEq1633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1633 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1633 + difference 0 0) (sourceB1633 + difference 0 0) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1633 + difference 0 0) (sourceB1633 + difference 0 0) sourceC1633) = raw23953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw23953; decide +kernel
    rw [ha]
    exact (canonical23953 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1633 + difference 1 0) (sourceB1633 + difference 0 1) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1633 + difference 1 0) (sourceB1633 + difference 0 1) sourceC1633) = raw23853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw23853; decide +kernel
    rw [ha]
    exact (canonical23853 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1633 + difference 2 0) (sourceB1633 + difference 0 2) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1594) := by
    have ha : (tripleCharges (sourceA1633 + difference 2 0) (sourceB1633 + difference 0 2) sourceC1633) = raw24032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw24032; decide +kernel
    rw [ha]
    exact (canonical24032 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1633 + difference 3 0) (sourceB1633 + difference 0 3) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1633 + difference 3 0) (sourceB1633 + difference 0 3) sourceC1633) = raw24033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw24033; decide +kernel
    rw [ha]
    exact (canonical24033 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1633 + difference 4 0) (sourceB1633 + difference 0 4) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1633 + difference 4 0) (sourceB1633 + difference 0 4) sourceC1633) = raw24034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw24034; decide +kernel
    rw [ha]
    exact (canonical24034 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1633 + difference 5 0) (sourceB1633 + difference 0 5) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1592) := by
    have ha : (tripleCharges (sourceA1633 + difference 5 0) (sourceB1633 + difference 0 5) sourceC1633) = raw24035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw24035; decide +kernel
    rw [ha]
    exact (canonical24035 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1633 + sourceB1633) sourceC1633) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1633 + sourceB1633) sourceC1633) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1633 sourceB1633 sourceC1633 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1633 sourceB1633 sourceC1633
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1633, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1634 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceB1634 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1634 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1634 : Integer.Sparse Master := [(Sum.inr 1597, 1), (Sum.inr 3238, 1), (Sum.inr 3285, 1), (Sum.inr 3288, 1), (Sum.inr 3290, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

theorem sourceEq1634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1634 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 0) (sourceB1634 + difference 0 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 0) (sourceB1634 + difference 0 3) sourceC1634) = raw24033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw24033; decide +kernel
    rw [ha]
    exact (canonical24033 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 1) (sourceB1634 + difference 1 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3238) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 1) (sourceB1634 + difference 1 3) sourceC1634) = raw24036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw24036; decide +kernel
    rw [ha]
    exact (canonical24036 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 2) (sourceB1634 + difference 2 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 2) (sourceB1634 + difference 2 3) sourceC1634) = raw23952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw23952; decide +kernel
    rw [ha]
    exact (canonical23952 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 3) (sourceB1634 + difference 3 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 3) (sourceB1634 + difference 3 3) sourceC1634) = raw23953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw23953; decide +kernel
    rw [ha]
    exact (canonical23953 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 4) (sourceB1634 + difference 4 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 4) (sourceB1634 + difference 4 3) sourceC1634) = raw24037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw24037; decide +kernel
    rw [ha]
    exact (canonical24037 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 5) (sourceB1634 + difference 5 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 5) (sourceB1634 + difference 5 3) sourceC1634) = raw24038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw24038; decide +kernel
    rw [ha]
    exact (canonical24038 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1634 + sourceB1634) sourceC1634) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1634 + sourceB1634) sourceC1634) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1634 sourceB1634 sourceC1634 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1634 sourceB1634 sourceC1634
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1634, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1635 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceB1635 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1635 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1635 : Integer.Sparse Master := [(Sum.inr 1616, 1), (Sum.inr 3241, 1), (Sum.inr 3288, 1), (Sum.inr 3290, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

theorem sourceEq1635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1635 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1635 + difference 0 5) (sourceB1635 + difference 5 0) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1616) := by
    have ha : (tripleCharges (sourceA1635 + difference 0 5) (sourceB1635 + difference 5 0) sourceC1635) = raw24031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw24031; decide +kernel
    rw [ha]
    exact (canonical24031 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1635 + difference 1 5) (sourceB1635 + difference 5 1) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1635 + difference 1 5) (sourceB1635 + difference 5 1) sourceC1635) = raw23847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw23847; decide +kernel
    rw [ha]
    exact (canonical23847 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1635 + difference 2 5) (sourceB1635 + difference 5 2) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3241) := by
    have ha : (tripleCharges (sourceA1635 + difference 2 5) (sourceB1635 + difference 5 2) sourceC1635) = raw23846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw23846; decide +kernel
    rw [ha]
    exact (canonical23846 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1635 + difference 3 5) (sourceB1635 + difference 5 3) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1635 + difference 3 5) (sourceB1635 + difference 5 3) sourceC1635) = raw24038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw24038; decide +kernel
    rw [ha]
    exact (canonical24038 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1635 + difference 4 5) (sourceB1635 + difference 5 4) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1635 + difference 4 5) (sourceB1635 + difference 5 4) sourceC1635) = raw23982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw23982; decide +kernel
    rw [ha]
    exact (canonical23982 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1635 + difference 5 5) (sourceB1635 + difference 5 5) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1635 + difference 5 5) (sourceB1635 + difference 5 5) sourceC1635) = raw23953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw23953; decide +kernel
    rw [ha]
    exact (canonical23953 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1635 + sourceB1635) sourceC1635) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1635 + sourceB1635) sourceC1635) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1635 sourceB1635 sourceC1635 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1635 sourceB1635 sourceC1635
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1635, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1636 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1636 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC1636 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceForm1636 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 1114, 1), (Sum.inr 1117, 1), (Sum.inr 1129, 1), (Sum.inr 1213, 1), (Sum.inr 2480, 1), (Sum.inr 4091, -1)]

theorem sourceEq1636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1636 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1636 + difference 0 1) (sourceB1636 + difference 1 0) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA1636 + difference 0 1) (sourceB1636 + difference 1 0) sourceC1636) = raw24039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24039; decide +kernel
    rw [ha]
    exact (canonical24039 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1636 + difference 1 1) (sourceB1636 + difference 1 1) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1636 + difference 1 1) (sourceB1636 + difference 1 1) sourceC1636) = raw24040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24040; decide +kernel
    rw [ha]
    exact (canonical24040 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1636 + difference 2 1) (sourceB1636 + difference 1 2) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1129) := by
    have ha : (tripleCharges (sourceA1636 + difference 2 1) (sourceB1636 + difference 1 2) sourceC1636) = raw24041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24041; decide +kernel
    rw [ha]
    exact (canonical24041 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1636 + difference 3 1) (sourceB1636 + difference 1 3) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA1636 + difference 3 1) (sourceB1636 + difference 1 3) sourceC1636) = raw24042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24042; decide +kernel
    rw [ha]
    exact (canonical24042 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1636 + difference 4 1) (sourceB1636 + difference 1 4) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1114) := by
    have ha : (tripleCharges (sourceA1636 + difference 4 1) (sourceB1636 + difference 1 4) sourceC1636) = raw24043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24043; decide +kernel
    rw [ha]
    exact (canonical24043 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1636 + difference 5 1) (sourceB1636 + difference 1 5) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1112) := by
    have ha : (tripleCharges (sourceA1636 + difference 5 1) (sourceB1636 + difference 1 5) sourceC1636) = raw24044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24044; decide +kernel
    rw [ha]
    exact (canonical24044 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1636 + sourceB1636) sourceC1636) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1636 + sourceB1636) sourceC1636) = raw24045 := by
      apply Matrix.ext; unfold doubleCharges sourceA1636 sourceB1636 sourceC1636 raw24045; decide +kernel
    rw [ha]
    exact (canonical24045 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1636 sourceB1636 sourceC1636
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1636, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1637 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1637 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC1637 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceForm1637 : Integer.Sparse Master := [(Sum.inr 625, 1), (Sum.inr 1129, 1), (Sum.inr 1213, 2), (Sum.inr 1235, 1), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

theorem sourceEq1637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1637 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 0) (sourceB1637 + difference 0 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 625) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 0) (sourceB1637 + difference 0 2) sourceC1637) = raw24046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24046; decide +kernel
    rw [ha]
    exact (canonical24046 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 1) (sourceB1637 + difference 1 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1129) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 1) (sourceB1637 + difference 1 2) sourceC1637) = raw24041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24041; decide +kernel
    rw [ha]
    exact (canonical24041 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 2) (sourceB1637 + difference 2 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 2) (sourceB1637 + difference 2 2) sourceC1637) = raw24040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24040; decide +kernel
    rw [ha]
    exact (canonical24040 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 3) (sourceB1637 + difference 3 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 3) (sourceB1637 + difference 3 2) sourceC1637) = raw24047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24047; decide +kernel
    rw [ha]
    exact (canonical24047 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 4) (sourceB1637 + difference 4 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 4) (sourceB1637 + difference 4 2) sourceC1637) = raw24048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24048; decide +kernel
    rw [ha]
    exact (canonical24048 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 5) (sourceB1637 + difference 5 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 5) (sourceB1637 + difference 5 2) sourceC1637) = raw24049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24049; decide +kernel
    rw [ha]
    exact (canonical24049 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1637 + sourceB1637) sourceC1637) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1637 + sourceB1637) sourceC1637) = raw24045 := by
      apply Matrix.ext; unfold doubleCharges sourceA1637 sourceB1637 sourceC1637 raw24045; decide +kernel
    rw [ha]
    exact (canonical24045 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1637 sourceB1637 sourceC1637
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1637, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1638 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceB1638 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC1638 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1638 : Integer.Sparse Master := [(Sum.inr 1597, 1), (Sum.inr 1598, 1), (Sum.inr 1601, 1), (Sum.inr 1616, 1), (Sum.inr 1724, 1), (Sum.inr 3290, 1), (Sum.inr 4069, -1)]

theorem sourceEq1638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1638 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 0) (sourceB1638 + difference 0 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 0) (sourceB1638 + difference 0 0) sourceC1638) = raw23982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw23982; decide +kernel
    rw [ha]
    exact (canonical23982 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 1) (sourceB1638 + difference 1 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1601) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 1) (sourceB1638 + difference 1 0) sourceC1638) = raw24050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw24050; decide +kernel
    rw [ha]
    exact (canonical24050 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 2) (sourceB1638 + difference 2 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 2) (sourceB1638 + difference 2 0) sourceC1638) = raw23970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw23970; decide +kernel
    rw [ha]
    exact (canonical23970 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 3) (sourceB1638 + difference 3 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1598) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 3) (sourceB1638 + difference 3 0) sourceC1638) = raw24051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw24051; decide +kernel
    rw [ha]
    exact (canonical24051 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 4) (sourceB1638 + difference 4 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1616) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 4) (sourceB1638 + difference 4 0) sourceC1638) = raw24031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw24031; decide +kernel
    rw [ha]
    exact (canonical24031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 5) (sourceB1638 + difference 5 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 5) (sourceB1638 + difference 5 0) sourceC1638) = raw24052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw24052; decide +kernel
    rw [ha]
    exact (canonical24052 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1638 + sourceB1638) sourceC1638) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1638 + sourceB1638) sourceC1638) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1638 sourceB1638 sourceC1638 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1638 sourceB1638 sourceC1638
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1638, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1639 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1639 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceC1639 : Charge := ![2, -1, 1, -1, 1, -2]
def sourceForm1639 : Integer.Sparse Master := [(Sum.inr 1210, 1), (Sum.inr 2477, 1), (Sum.inr 2613, 1), (Sum.inr 2694, 1), (Sum.inr 2708, 1), (Sum.inr 2718, 1), (Sum.inr 4090, -1)]

theorem sourceEq1639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1639 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 0) (sourceB1639 + difference 0 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 0) (sourceB1639 + difference 0 0) sourceC1639) = raw24053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24053; decide +kernel
    rw [ha]
    exact (canonical24053 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 1) (sourceB1639 + difference 1 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2613) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 1) (sourceB1639 + difference 1 0) sourceC1639) = raw24054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24054; decide +kernel
    rw [ha]
    exact (canonical24054 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 2) (sourceB1639 + difference 2 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 2) (sourceB1639 + difference 2 0) sourceC1639) = raw24055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24055; decide +kernel
    rw [ha]
    exact (canonical24055 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 3) (sourceB1639 + difference 3 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 3) (sourceB1639 + difference 3 0) sourceC1639) = raw24056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24056; decide +kernel
    rw [ha]
    exact (canonical24056 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 4) (sourceB1639 + difference 4 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 4) (sourceB1639 + difference 4 0) sourceC1639) = raw24057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24057; decide +kernel
    rw [ha]
    exact (canonical24057 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 5) (sourceB1639 + difference 5 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 5) (sourceB1639 + difference 5 0) sourceC1639) = raw24058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24058; decide +kernel
    rw [ha]
    exact (canonical24058 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1639 + sourceB1639) sourceC1639) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1639 + sourceB1639) sourceC1639) = raw24059 := by
      apply Matrix.ext; unfold doubleCharges sourceA1639 sourceB1639 sourceC1639 raw24059; decide +kernel
    rw [ha]
    exact (canonical24059 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1639 sourceB1639 sourceC1639
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1639, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1640 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1640 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC1640 : Charge := ![2, -1, 2, -1, -1, -1]
def sourceForm1640 : Integer.Sparse Master := [(Sum.inr 1180, 1), (Sum.inr 2383, 1), (Sum.inr 2607, 1), (Sum.inr 2662, 2), (Sum.inr 2671, 1), (Sum.inr 4087, -1)]

theorem sourceEq1640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1640 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 0) (sourceB1640 + difference 0 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 0) (sourceB1640 + difference 0 0) sourceC1640) = raw24060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24060; decide +kernel
    rw [ha]
    exact (canonical24060 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 1) (sourceB1640 + difference 1 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2607) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 1) (sourceB1640 + difference 1 0) sourceC1640) = raw24061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24061; decide +kernel
    rw [ha]
    exact (canonical24061 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 2) (sourceB1640 + difference 2 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2383) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 2) (sourceB1640 + difference 2 0) sourceC1640) = raw24062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24062; decide +kernel
    rw [ha]
    exact (canonical24062 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 3) (sourceB1640 + difference 3 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 3) (sourceB1640 + difference 3 0) sourceC1640) = raw24063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24063; decide +kernel
    rw [ha]
    exact (canonical24063 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 4) (sourceB1640 + difference 4 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 4) (sourceB1640 + difference 4 0) sourceC1640) = raw24064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24064; decide +kernel
    rw [ha]
    exact (canonical24064 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 5) (sourceB1640 + difference 5 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 5) (sourceB1640 + difference 5 0) sourceC1640) = raw24065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24065; decide +kernel
    rw [ha]
    exact (canonical24065 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1640 + sourceB1640) sourceC1640) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1640 + sourceB1640) sourceC1640) = raw24066 := by
      apply Matrix.ext; unfold doubleCharges sourceA1640 sourceB1640 sourceC1640 raw24066; decide +kernel
    rw [ha]
    exact (canonical24066 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1640 sourceB1640 sourceC1640
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1640, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1641 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1641 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC1641 : Charge := ![2, -1, 2, -1, -1, -1]
def sourceForm1641 : Integer.Sparse Master := [(Sum.inr 1180, 3), (Sum.inr 1187, 1), (Sum.inr 1256, 1), (Sum.inr 2671, 1), (Sum.inr 4087, -1)]

theorem sourceEq1641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1641 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1641 + difference 0 5) (sourceB1641 + difference 5 0) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1641 + difference 0 5) (sourceB1641 + difference 5 0) sourceC1641) = raw24065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24065; decide +kernel
    rw [ha]
    exact (canonical24065 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1641 + difference 1 5) (sourceB1641 + difference 5 1) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1187) := by
    have ha : (tripleCharges (sourceA1641 + difference 1 5) (sourceB1641 + difference 5 1) sourceC1641) = raw24067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24067; decide +kernel
    rw [ha]
    exact (canonical24067 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1641 + difference 2 5) (sourceB1641 + difference 5 2) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1256) := by
    have ha : (tripleCharges (sourceA1641 + difference 2 5) (sourceB1641 + difference 5 2) sourceC1641) = raw24068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24068; decide +kernel
    rw [ha]
    exact (canonical24068 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1641 + difference 3 5) (sourceB1641 + difference 5 3) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA1641 + difference 3 5) (sourceB1641 + difference 5 3) sourceC1641) = raw24069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24069; decide +kernel
    rw [ha]
    exact (canonical24069 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1641 + difference 4 5) (sourceB1641 + difference 5 4) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA1641 + difference 4 5) (sourceB1641 + difference 5 4) sourceC1641) = raw24070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24070; decide +kernel
    rw [ha]
    exact (canonical24070 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1641 + difference 5 5) (sourceB1641 + difference 5 5) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA1641 + difference 5 5) (sourceB1641 + difference 5 5) sourceC1641) = raw24060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24060; decide +kernel
    rw [ha]
    exact (canonical24060 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1641 + sourceB1641) sourceC1641) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1641 + sourceB1641) sourceC1641) = raw24066 := by
      apply Matrix.ext; unfold doubleCharges sourceA1641 sourceB1641 sourceC1641 raw24066; decide +kernel
    rw [ha]
    exact (canonical24066 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1641 sourceB1641 sourceC1641
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1641, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1642 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1642 : Charge := ![2, 1, -2, 0, -1, 0]
def sourceC1642 : Charge := ![2, -1, 2, -1, 0, -2]
def sourceForm1642 : Integer.Sparse Master := [(Sum.inr 1178, 1), (Sum.inr 2382, 1), (Sum.inr 2606, 1), (Sum.inr 2661, 1), (Sum.inr 2669, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

theorem sourceEq1642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1642 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 0) (sourceB1642 + difference 0 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1178) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 0) (sourceB1642 + difference 0 0) sourceC1642) = raw24071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24071; decide +kernel
    rw [ha]
    exact (canonical24071 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 1) (sourceB1642 + difference 1 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2606) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 1) (sourceB1642 + difference 1 0) sourceC1642) = raw24072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24072; decide +kernel
    rw [ha]
    exact (canonical24072 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 2) (sourceB1642 + difference 2 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 2) (sourceB1642 + difference 2 0) sourceC1642) = raw24073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24073; decide +kernel
    rw [ha]
    exact (canonical24073 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 3) (sourceB1642 + difference 3 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 3) (sourceB1642 + difference 3 0) sourceC1642) = raw24074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24074; decide +kernel
    rw [ha]
    exact (canonical24074 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 4) (sourceB1642 + difference 4 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 4) (sourceB1642 + difference 4 0) sourceC1642) = raw24075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24075; decide +kernel
    rw [ha]
    exact (canonical24075 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 5) (sourceB1642 + difference 5 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 5) (sourceB1642 + difference 5 0) sourceC1642) = raw24076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24076; decide +kernel
    rw [ha]
    exact (canonical24076 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1642 + sourceB1642) sourceC1642) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1642 + sourceB1642) sourceC1642) = raw24077 := by
      apply Matrix.ext; unfold doubleCharges sourceA1642 sourceB1642 sourceC1642 raw24077; decide +kernel
    rw [ha]
    exact (canonical24077 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1642 sourceB1642 sourceC1642
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1642, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1643 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceB1643 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1643 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1643 : Integer.Sparse Master := [(Sum.inr 1656, 2), (Sum.inr 1659, 1), (Sum.inr 1661, 1), (Sum.inr 1739, 1), (Sum.inr 2737, 1), (Sum.inr 4069, -1)]

theorem sourceEq1643 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1643 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 0) (sourceB1643 + difference 0 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 0) (sourceB1643 + difference 0 0) sourceC1643) = raw23945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw23945; decide +kernel
    rw [ha]
    exact (canonical23945 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 1) (sourceB1643 + difference 1 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 1) (sourceB1643 + difference 1 0) sourceC1643) = raw23940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw23940; decide +kernel
    rw [ha]
    exact (canonical23940 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 2) (sourceB1643 + difference 2 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 2) (sourceB1643 + difference 2 0) sourceC1643) = raw24078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw24078; decide +kernel
    rw [ha]
    exact (canonical24078 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 3) (sourceB1643 + difference 3 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1659) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 3) (sourceB1643 + difference 3 0) sourceC1643) = raw24079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw24079; decide +kernel
    rw [ha]
    exact (canonical24079 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 4) (sourceB1643 + difference 4 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1661) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 4) (sourceB1643 + difference 4 0) sourceC1643) = raw24080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw24080; decide +kernel
    rw [ha]
    exact (canonical24080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 5) (sourceB1643 + difference 5 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 5) (sourceB1643 + difference 5 0) sourceC1643) = raw24081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw24081; decide +kernel
    rw [ha]
    exact (canonical24081 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1643 + sourceB1643) sourceC1643) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1643 + sourceB1643) sourceC1643) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1643 sourceB1643 sourceC1643 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1643 sourceB1643 sourceC1643
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1643, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1644 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceB1644 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1644 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1644 : Integer.Sparse Master := [(Sum.inr 1650, 1), (Sum.inr 2502, 2), (Sum.inr 2521, 1), (Sum.inr 2737, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

theorem sourceEq1644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1644 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 0) (sourceB1644 + difference 0 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 0) (sourceB1644 + difference 0 4) sourceC1644) = raw24082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw24082; decide +kernel
    rw [ha]
    exact (canonical24082 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 1) (sourceB1644 + difference 1 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 1) (sourceB1644 + difference 1 4) sourceC1644) = raw24083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw24083; decide +kernel
    rw [ha]
    exact (canonical24083 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 2) (sourceB1644 + difference 2 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 2) (sourceB1644 + difference 2 4) sourceC1644) = raw24084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw24084; decide +kernel
    rw [ha]
    exact (canonical24084 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 3) (sourceB1644 + difference 3 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2521) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 3) (sourceB1644 + difference 3 4) sourceC1644) = raw24085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw24085; decide +kernel
    rw [ha]
    exact (canonical24085 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 4) (sourceB1644 + difference 4 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 4) (sourceB1644 + difference 4 4) sourceC1644) = raw23945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw23945; decide +kernel
    rw [ha]
    exact (canonical23945 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 5) (sourceB1644 + difference 5 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 5) (sourceB1644 + difference 5 4) sourceC1644) = raw24086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw24086; decide +kernel
    rw [ha]
    exact (canonical24086 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1644 + sourceB1644) sourceC1644) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1644 + sourceB1644) sourceC1644) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1644 sourceB1644 sourceC1644 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1644 sourceB1644 sourceC1644
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1644, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1645 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceB1645 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1645 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1645 : Integer.Sparse Master := [(Sum.inr 1646, 2), (Sum.inr 1651, 1), (Sum.inr 1653, 1), (Sum.inr 1728, 1), (Sum.inr 3306, 1), (Sum.inr 4069, -1)]

theorem sourceEq1645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1645 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 0) (sourceB1645 + difference 0 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 0) (sourceB1645 + difference 0 0) sourceC1645) = raw23976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw23976; decide +kernel
    rw [ha]
    exact (canonical23976 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 1) (sourceB1645 + difference 1 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1646) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 1) (sourceB1645 + difference 1 0) sourceC1645) = raw23969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw23969; decide +kernel
    rw [ha]
    exact (canonical23969 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 2) (sourceB1645 + difference 2 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1646) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 2) (sourceB1645 + difference 2 0) sourceC1645) = raw24087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw24087; decide +kernel
    rw [ha]
    exact (canonical24087 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 3) (sourceB1645 + difference 3 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1651) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 3) (sourceB1645 + difference 3 0) sourceC1645) = raw24088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw24088; decide +kernel
    rw [ha]
    exact (canonical24088 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 4) (sourceB1645 + difference 4 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 4) (sourceB1645 + difference 4 0) sourceC1645) = raw24089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw24089; decide +kernel
    rw [ha]
    exact (canonical24089 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 5) (sourceB1645 + difference 5 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 5) (sourceB1645 + difference 5 0) sourceC1645) = raw24090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw24090; decide +kernel
    rw [ha]
    exact (canonical24090 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1645 + sourceB1645) sourceC1645) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1645 + sourceB1645) sourceC1645) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1645 sourceB1645 sourceC1645 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1645 sourceB1645 sourceC1645
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1645, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1646 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceB1646 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1646 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1646 : Integer.Sparse Master := [(Sum.inr 1653, 1), (Sum.inr 3049, 1), (Sum.inr 3287, 2), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 4069, -1)]

theorem sourceEq1646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1646 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 0) (sourceB1646 + difference 0 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 0) (sourceB1646 + difference 0 5) sourceC1646) = raw24091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw24091; decide +kernel
    rw [ha]
    exact (canonical24091 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 1) (sourceB1646 + difference 1 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3287) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 1) (sourceB1646 + difference 1 5) sourceC1646) = raw23985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw23985; decide +kernel
    rw [ha]
    exact (canonical23985 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 2) (sourceB1646 + difference 2 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3287) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 2) (sourceB1646 + difference 2 5) sourceC1646) = raw24092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw24092; decide +kernel
    rw [ha]
    exact (canonical24092 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 3) (sourceB1646 + difference 3 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3049) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 3) (sourceB1646 + difference 3 5) sourceC1646) = raw24093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw24093; decide +kernel
    rw [ha]
    exact (canonical24093 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 4) (sourceB1646 + difference 4 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 4) (sourceB1646 + difference 4 5) sourceC1646) = raw24086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw24086; decide +kernel
    rw [ha]
    exact (canonical24086 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 5) (sourceB1646 + difference 5 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 5) (sourceB1646 + difference 5 5) sourceC1646) = raw23976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw23976; decide +kernel
    rw [ha]
    exact (canonical23976 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1646 + sourceB1646) sourceC1646) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1646 + sourceB1646) sourceC1646) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1646 sourceB1646 sourceC1646 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1646 sourceB1646 sourceC1646
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1646, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1647 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1647 : Charge := ![2, 0, 0, 1, -3, 0]
def sourceC1647 : Charge := ![2, 0, 0, -2, 2, -2]
def sourceForm1647 : Integer.Sparse Master := [(Sum.inr 1288, 1), (Sum.inr 2585, 2), (Sum.inr 2686, 1), (Sum.inr 2771, 1), (Sum.inr 2779, 1), (Sum.inr 4089, -1)]

theorem sourceEq1647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1647 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 0) (sourceB1647 + difference 0 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1288) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 0) (sourceB1647 + difference 0 0) sourceC1647) = raw24094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24094; decide +kernel
    rw [ha]
    exact (canonical24094 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 1) (sourceB1647 + difference 1 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2585) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 1) (sourceB1647 + difference 1 0) sourceC1647) = raw24095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24095; decide +kernel
    rw [ha]
    exact (canonical24095 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 2) (sourceB1647 + difference 2 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2585) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 2) (sourceB1647 + difference 2 0) sourceC1647) = raw24096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24096; decide +kernel
    rw [ha]
    exact (canonical24096 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 3) (sourceB1647 + difference 3 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2771) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 3) (sourceB1647 + difference 3 0) sourceC1647) = raw24097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24097; decide +kernel
    rw [ha]
    exact (canonical24097 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 4) (sourceB1647 + difference 4 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 4) (sourceB1647 + difference 4 0) sourceC1647) = raw24098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24098; decide +kernel
    rw [ha]
    exact (canonical24098 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 5) (sourceB1647 + difference 5 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2779) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 5) (sourceB1647 + difference 5 0) sourceC1647) = raw24099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24099; decide +kernel
    rw [ha]
    exact (canonical24099 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1647 + sourceB1647) sourceC1647) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1647 + sourceB1647) sourceC1647) = raw24100 := by
      apply Matrix.ext; unfold doubleCharges sourceA1647 sourceB1647 sourceC1647 raw24100; decide +kernel
    rw [ha]
    exact (canonical24100 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1647 sourceB1647 sourceC1647
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1647, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1648 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1648 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1648 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1648 : Integer.Sparse Master := [(Sum.inr 4182, 2), (Sum.inr 4183, 1), (Sum.inr 4185, 2), (Sum.inr 4550, 2), (Sum.inr 4551, 2), (Sum.inr 4553, 4), (Sum.inr 4618, 2), (Sum.inr 4619, 2), (Sum.inr 4623, 4), (Sum.inr 4625, 2), (Sum.inr 4627, 2), (Sum.inr 5168, 2), (Sum.inr 5306, 1), (Sum.inr 5308, 2)]

theorem sourceEq1648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1648 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1648 + difference 0 1) (sourceB1648 + difference 1 0) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1648 + difference 0 1) (sourceB1648 + difference 1 0) sourceC1648) = raw10229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw10229; decide +kernel
    rw [ha]
    exact (canonical10229 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1648 + difference 0 2) (sourceB1648 + difference 2 0) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1648 + difference 0 2) (sourceB1648 + difference 2 0) sourceC1648) = raw10230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw10230; decide +kernel
    rw [ha]
    exact (canonical10230 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1648 + difference 0 3) (sourceB1648 + difference 3 0) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA1648 + difference 0 3) (sourceB1648 + difference 3 0) sourceC1648) = raw5082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw5082; decide +kernel
    rw [ha]
    exact (canonical5082 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1648 + difference 0 4) (sourceB1648 + difference 4 0) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA1648 + difference 0 4) (sourceB1648 + difference 4 0) sourceC1648) = raw5077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw5077; decide +kernel
    rw [ha]
    exact (canonical5077 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1648 + difference 0 5) (sourceB1648 + difference 5 0) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA1648 + difference 0 5) (sourceB1648 + difference 5 0) sourceC1648) = raw10231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw10231; decide +kernel
    rw [ha]
    exact (canonical10231 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1648 + difference 1 0) (sourceB1648 + difference 0 1) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4182) := by
    have ha : (tripleCharges (sourceA1648 + difference 1 0) (sourceB1648 + difference 0 1) sourceC1648) = raw24101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw24101; decide +kernel
    rw [ha]
    exact (canonical24101 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1648 + difference 1 2) (sourceB1648 + difference 2 1) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4550) := by
    have ha : (tripleCharges (sourceA1648 + difference 1 2) (sourceB1648 + difference 2 1) sourceC1648) = raw24102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw24102; decide +kernel
    rw [ha]
    exact (canonical24102 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1648 + difference 1 3) (sourceB1648 + difference 3 1) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1648 + difference 1 3) (sourceB1648 + difference 3 1) sourceC1648) = raw10220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw10220; decide +kernel
    rw [ha]
    exact (canonical10220 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1648 + difference 1 4) (sourceB1648 + difference 4 1) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1648 + difference 1 4) (sourceB1648 + difference 4 1) sourceC1648) = raw24103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw24103; decide +kernel
    rw [ha]
    exact (canonical24103 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1648 + difference 1 5) (sourceB1648 + difference 5 1) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1648 + difference 1 5) (sourceB1648 + difference 5 1) sourceC1648) = raw12084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw12084; decide +kernel
    rw [ha]
    exact (canonical12084 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1648 + difference 2 0) (sourceB1648 + difference 0 2) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4182) := by
    have ha : (tripleCharges (sourceA1648 + difference 2 0) (sourceB1648 + difference 0 2) sourceC1648) = raw24104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw24104; decide +kernel
    rw [ha]
    exact (canonical24104 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1648 + difference 2 1) (sourceB1648 + difference 1 2) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4550) := by
    have ha : (tripleCharges (sourceA1648 + difference 2 1) (sourceB1648 + difference 1 2) sourceC1648) = raw24105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw24105; decide +kernel
    rw [ha]
    exact (canonical24105 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1648 + difference 2 3) (sourceB1648 + difference 3 2) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1648 + difference 2 3) (sourceB1648 + difference 3 2) sourceC1648) = raw10224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw10224; decide +kernel
    rw [ha]
    exact (canonical10224 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1648 + difference 2 4) (sourceB1648 + difference 4 2) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1648 + difference 2 4) (sourceB1648 + difference 4 2) sourceC1648) = raw24106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw24106; decide +kernel
    rw [ha]
    exact (canonical24106 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1648 + difference 2 5) (sourceB1648 + difference 5 2) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1648 + difference 2 5) (sourceB1648 + difference 5 2) sourceC1648) = raw12088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw12088; decide +kernel
    rw [ha]
    exact (canonical12088 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1648 + difference 3 0) (sourceB1648 + difference 0 3) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4185) := by
    have ha : (tripleCharges (sourceA1648 + difference 3 0) (sourceB1648 + difference 0 3) sourceC1648) = raw24107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw24107; decide +kernel
    rw [ha]
    exact (canonical24107 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1648 + difference 3 1) (sourceB1648 + difference 1 3) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1648 + difference 3 1) (sourceB1648 + difference 1 3) sourceC1648) = raw24108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw24108; decide +kernel
    rw [ha]
    exact (canonical24108 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1648 + difference 3 2) (sourceB1648 + difference 2 3) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1648 + difference 3 2) (sourceB1648 + difference 2 3) sourceC1648) = raw24109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw24109; decide +kernel
    rw [ha]
    exact (canonical24109 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1648 + difference 3 4) (sourceB1648 + difference 4 3) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1648 + difference 3 4) (sourceB1648 + difference 4 3) sourceC1648) = raw24110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw24110; decide +kernel
    rw [ha]
    exact (canonical24110 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1648 + difference 3 5) (sourceB1648 + difference 5 3) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1648 + difference 3 5) (sourceB1648 + difference 5 3) sourceC1648) = raw12092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw12092; decide +kernel
    rw [ha]
    exact (canonical12092 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1648 + difference 4 0) (sourceB1648 + difference 0 4) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4185) := by
    have ha : (tripleCharges (sourceA1648 + difference 4 0) (sourceB1648 + difference 0 4) sourceC1648) = raw22479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw22479; decide +kernel
    rw [ha]
    exact (canonical22479 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1648 + difference 4 1) (sourceB1648 + difference 1 4) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1648 + difference 4 1) (sourceB1648 + difference 1 4) sourceC1648) = raw22480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw22480; decide +kernel
    rw [ha]
    exact (canonical22480 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1648 + difference 4 2) (sourceB1648 + difference 2 4) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1648 + difference 4 2) (sourceB1648 + difference 2 4) sourceC1648) = raw22481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw22481; decide +kernel
    rw [ha]
    exact (canonical22481 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1648 + difference 4 3) (sourceB1648 + difference 3 4) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1648 + difference 4 3) (sourceB1648 + difference 3 4) sourceC1648) = raw10232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw10232; decide +kernel
    rw [ha]
    exact (canonical10232 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1648 + difference 4 5) (sourceB1648 + difference 5 4) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1648 + difference 4 5) (sourceB1648 + difference 5 4) sourceC1648) = raw12097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw12097; decide +kernel
    rw [ha]
    exact (canonical12097 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1648 + difference 5 0) (sourceB1648 + difference 0 5) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4183) := by
    have ha : (tripleCharges (sourceA1648 + difference 5 0) (sourceB1648 + difference 0 5) sourceC1648) = raw20357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw20357; decide +kernel
    rw [ha]
    exact (canonical20357 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1648 + difference 5 1) (sourceB1648 + difference 1 5) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1648 + difference 5 1) (sourceB1648 + difference 1 5) sourceC1648) = raw20358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw20358; decide +kernel
    rw [ha]
    exact (canonical20358 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1648 + difference 5 2) (sourceB1648 + difference 2 5) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1648 + difference 5 2) (sourceB1648 + difference 2 5) sourceC1648) = raw20359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw20359; decide +kernel
    rw [ha]
    exact (canonical20359 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1648 + difference 5 3) (sourceB1648 + difference 3 5) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1648 + difference 5 3) (sourceB1648 + difference 3 5) sourceC1648) = raw5078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw5078; decide +kernel
    rw [ha]
    exact (canonical5078 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1648 + difference 5 4) (sourceB1648 + difference 4 5) sourceC1648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1648 + difference 5 4) (sourceB1648 + difference 4 5) sourceC1648) = raw5073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1648 sourceB1648 sourceC1648 difference raw5073; decide +kernel
    rw [ha]
    exact (canonical5073 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1648 sourceB1648 sourceC1648
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1648, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1649 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1649 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1649 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1649 : Integer.Sparse Master := [(Sum.inr 610, 2), (Sum.inr 611, 1), (Sum.inr 613, 2), (Sum.inr 1135, 2), (Sum.inr 1136, 2), (Sum.inr 1138, 4), (Sum.inr 1293, 2), (Sum.inr 1294, 2), (Sum.inr 1305, 4), (Sum.inr 1307, 2), (Sum.inr 1311, 2), (Sum.inr 2963, 2), (Sum.inr 3120, 1), (Sum.inr 3124, 2)]

theorem sourceEq1649 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1649 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1649 + difference 0 1) (sourceB1649 + difference 1 0) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA1649 + difference 0 1) (sourceB1649 + difference 1 0) sourceC1649) = raw12127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw12127; decide +kernel
    rw [ha]
    exact (canonical12127 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1649 + difference 0 2) (sourceB1649 + difference 2 0) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA1649 + difference 0 2) (sourceB1649 + difference 2 0) sourceC1649) = raw12128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw12128; decide +kernel
    rw [ha]
    exact (canonical12128 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1649 + difference 0 3) (sourceB1649 + difference 3 0) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA1649 + difference 0 3) (sourceB1649 + difference 3 0) sourceC1649) = raw12129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw12129; decide +kernel
    rw [ha]
    exact (canonical12129 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1649 + difference 0 4) (sourceB1649 + difference 4 0) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA1649 + difference 0 4) (sourceB1649 + difference 4 0) sourceC1649) = raw12130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw12130; decide +kernel
    rw [ha]
    exact (canonical12130 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1649 + difference 0 5) (sourceB1649 + difference 5 0) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA1649 + difference 0 5) (sourceB1649 + difference 5 0) sourceC1649) = raw24111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw24111; decide +kernel
    rw [ha]
    exact (canonical24111 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1649 + difference 1 0) (sourceB1649 + difference 0 1) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 610) := by
    have ha : (tripleCharges (sourceA1649 + difference 1 0) (sourceB1649 + difference 0 1) sourceC1649) = raw24112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw24112; decide +kernel
    rw [ha]
    exact (canonical24112 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1649 + difference 1 2) (sourceB1649 + difference 2 1) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1135) := by
    have ha : (tripleCharges (sourceA1649 + difference 1 2) (sourceB1649 + difference 2 1) sourceC1649) = raw24113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw24113; decide +kernel
    rw [ha]
    exact (canonical24113 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1649 + difference 1 3) (sourceB1649 + difference 3 1) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1649 + difference 1 3) (sourceB1649 + difference 3 1) sourceC1649) = raw20370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw20370; decide +kernel
    rw [ha]
    exact (canonical20370 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1649 + difference 1 4) (sourceB1649 + difference 4 1) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1649 + difference 1 4) (sourceB1649 + difference 4 1) sourceC1649) = raw24114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw24114; decide +kernel
    rw [ha]
    exact (canonical24114 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1649 + difference 1 5) (sourceB1649 + difference 5 1) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1649 + difference 1 5) (sourceB1649 + difference 5 1) sourceC1649) = raw12106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw12106; decide +kernel
    rw [ha]
    exact (canonical12106 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1649 + difference 2 0) (sourceB1649 + difference 0 2) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 610) := by
    have ha : (tripleCharges (sourceA1649 + difference 2 0) (sourceB1649 + difference 0 2) sourceC1649) = raw24115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw24115; decide +kernel
    rw [ha]
    exact (canonical24115 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1649 + difference 2 1) (sourceB1649 + difference 1 2) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1135) := by
    have ha : (tripleCharges (sourceA1649 + difference 2 1) (sourceB1649 + difference 1 2) sourceC1649) = raw24116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw24116; decide +kernel
    rw [ha]
    exact (canonical24116 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1649 + difference 2 3) (sourceB1649 + difference 3 2) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1649 + difference 2 3) (sourceB1649 + difference 3 2) sourceC1649) = raw20374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw20374; decide +kernel
    rw [ha]
    exact (canonical20374 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1649 + difference 2 4) (sourceB1649 + difference 4 2) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1649 + difference 2 4) (sourceB1649 + difference 4 2) sourceC1649) = raw24117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw24117; decide +kernel
    rw [ha]
    exact (canonical24117 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1649 + difference 2 5) (sourceB1649 + difference 5 2) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1649 + difference 2 5) (sourceB1649 + difference 5 2) sourceC1649) = raw12111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw12111; decide +kernel
    rw [ha]
    exact (canonical12111 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1649 + difference 3 0) (sourceB1649 + difference 0 3) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 613) := by
    have ha : (tripleCharges (sourceA1649 + difference 3 0) (sourceB1649 + difference 0 3) sourceC1649) = raw24118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw24118; decide +kernel
    rw [ha]
    exact (canonical24118 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1649 + difference 3 1) (sourceB1649 + difference 1 3) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1649 + difference 3 1) (sourceB1649 + difference 1 3) sourceC1649) = raw24119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw24119; decide +kernel
    rw [ha]
    exact (canonical24119 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1649 + difference 3 2) (sourceB1649 + difference 2 3) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1649 + difference 3 2) (sourceB1649 + difference 2 3) sourceC1649) = raw24120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw24120; decide +kernel
    rw [ha]
    exact (canonical24120 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1649 + difference 3 4) (sourceB1649 + difference 4 3) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1649 + difference 3 4) (sourceB1649 + difference 4 3) sourceC1649) = raw24121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw24121; decide +kernel
    rw [ha]
    exact (canonical24121 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1649 + difference 3 5) (sourceB1649 + difference 5 3) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1649 + difference 3 5) (sourceB1649 + difference 5 3) sourceC1649) = raw12116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw12116; decide +kernel
    rw [ha]
    exact (canonical12116 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1649 + difference 4 0) (sourceB1649 + difference 0 4) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 613) := by
    have ha : (tripleCharges (sourceA1649 + difference 4 0) (sourceB1649 + difference 0 4) sourceC1649) = raw22498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw22498; decide +kernel
    rw [ha]
    exact (canonical22498 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1649 + difference 4 1) (sourceB1649 + difference 1 4) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1649 + difference 4 1) (sourceB1649 + difference 1 4) sourceC1649) = raw22499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw22499; decide +kernel
    rw [ha]
    exact (canonical22499 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1649 + difference 4 2) (sourceB1649 + difference 2 4) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1649 + difference 4 2) (sourceB1649 + difference 2 4) sourceC1649) = raw22500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw22500; decide +kernel
    rw [ha]
    exact (canonical22500 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1649 + difference 4 3) (sourceB1649 + difference 3 4) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1649 + difference 4 3) (sourceB1649 + difference 3 4) sourceC1649) = raw20382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw20382; decide +kernel
    rw [ha]
    exact (canonical20382 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1649 + difference 4 5) (sourceB1649 + difference 5 4) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1649 + difference 4 5) (sourceB1649 + difference 5 4) sourceC1649) = raw12121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw12121; decide +kernel
    rw [ha]
    exact (canonical12121 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1649 + difference 5 0) (sourceB1649 + difference 0 5) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 611) := by
    have ha : (tripleCharges (sourceA1649 + difference 5 0) (sourceB1649 + difference 0 5) sourceC1649) = raw20375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw20375; decide +kernel
    rw [ha]
    exact (canonical20375 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1649 + difference 5 1) (sourceB1649 + difference 1 5) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1649 + difference 5 1) (sourceB1649 + difference 1 5) sourceC1649) = raw20376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw20376; decide +kernel
    rw [ha]
    exact (canonical20376 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1649 + difference 5 2) (sourceB1649 + difference 2 5) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1649 + difference 5 2) (sourceB1649 + difference 2 5) sourceC1649) = raw20377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw20377; decide +kernel
    rw [ha]
    exact (canonical20377 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1649 + difference 5 3) (sourceB1649 + difference 3 5) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1649 + difference 5 3) (sourceB1649 + difference 3 5) sourceC1649) = raw19549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw19549; decide +kernel
    rw [ha]
    exact (canonical19549 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1649 + difference 5 4) (sourceB1649 + difference 4 5) sourceC1649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1649 + difference 5 4) (sourceB1649 + difference 4 5) sourceC1649) = raw19544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1649 sourceB1649 sourceC1649 difference raw19544; decide +kernel
    rw [ha]
    exact (canonical19544 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1649 sourceB1649 sourceC1649
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1649, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1650 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1650 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1650 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm1650 : Integer.Sparse Master := [(Sum.inr 4172, 2), (Sum.inr 4174, 1), (Sum.inr 4180, 2), (Sum.inr 4541, 2), (Sum.inr 4543, 2), (Sum.inr 4549, 4), (Sum.inr 4602, 4), (Sum.inr 4605, 2), (Sum.inr 4612, 2), (Sum.inr 4622, 2), (Sum.inr 4624, 2), (Sum.inr 5172, 2), (Sum.inr 5294, 2), (Sum.inr 5307, 1)]

theorem sourceEq1650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1650 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1650 + difference 0 1) (sourceB1650 + difference 1 0) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1650 + difference 0 1) (sourceB1650 + difference 1 0) sourceC1650) = raw7977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw7977; decide +kernel
    rw [ha]
    exact (canonical7977 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1650 + difference 0 2) (sourceB1650 + difference 2 0) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1650 + difference 0 2) (sourceB1650 + difference 2 0) sourceC1650) = raw7978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw7978; decide +kernel
    rw [ha]
    exact (canonical7978 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1650 + difference 0 3) (sourceB1650 + difference 3 0) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1650 + difference 0 3) (sourceB1650 + difference 3 0) sourceC1650) = raw2681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw2681; decide +kernel
    rw [ha]
    exact (canonical2681 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1650 + difference 0 4) (sourceB1650 + difference 4 0) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1650 + difference 0 4) (sourceB1650 + difference 4 0) sourceC1650) = raw2676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw2676; decide +kernel
    rw [ha]
    exact (canonical2676 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1650 + difference 0 5) (sourceB1650 + difference 5 0) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA1650 + difference 0 5) (sourceB1650 + difference 5 0) sourceC1650) = raw7979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw7979; decide +kernel
    rw [ha]
    exact (canonical7979 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1650 + difference 1 0) (sourceB1650 + difference 0 1) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1650 + difference 1 0) (sourceB1650 + difference 0 1) sourceC1650) = raw24122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24122; decide +kernel
    rw [ha]
    exact (canonical24122 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1650 + difference 1 2) (sourceB1650 + difference 2 1) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4541) := by
    have ha : (tripleCharges (sourceA1650 + difference 1 2) (sourceB1650 + difference 2 1) sourceC1650) = raw24123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24123; decide +kernel
    rw [ha]
    exact (canonical24123 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1650 + difference 1 3) (sourceB1650 + difference 3 1) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1650 + difference 1 3) (sourceB1650 + difference 3 1) sourceC1650) = raw7968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw7968; decide +kernel
    rw [ha]
    exact (canonical7968 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1650 + difference 1 4) (sourceB1650 + difference 4 1) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1650 + difference 1 4) (sourceB1650 + difference 4 1) sourceC1650) = raw24124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24124; decide +kernel
    rw [ha]
    exact (canonical24124 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1650 + difference 1 5) (sourceB1650 + difference 5 1) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1650 + difference 1 5) (sourceB1650 + difference 5 1) sourceC1650) = raw14056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw14056; decide +kernel
    rw [ha]
    exact (canonical14056 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1650 + difference 2 0) (sourceB1650 + difference 0 2) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1650 + difference 2 0) (sourceB1650 + difference 0 2) sourceC1650) = raw24125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24125; decide +kernel
    rw [ha]
    exact (canonical24125 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1650 + difference 2 1) (sourceB1650 + difference 1 2) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4541) := by
    have ha : (tripleCharges (sourceA1650 + difference 2 1) (sourceB1650 + difference 1 2) sourceC1650) = raw24126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24126; decide +kernel
    rw [ha]
    exact (canonical24126 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1650 + difference 2 3) (sourceB1650 + difference 3 2) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1650 + difference 2 3) (sourceB1650 + difference 3 2) sourceC1650) = raw7972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw7972; decide +kernel
    rw [ha]
    exact (canonical7972 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1650 + difference 2 4) (sourceB1650 + difference 4 2) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1650 + difference 2 4) (sourceB1650 + difference 4 2) sourceC1650) = raw24127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24127; decide +kernel
    rw [ha]
    exact (canonical24127 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1650 + difference 2 5) (sourceB1650 + difference 5 2) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1650 + difference 2 5) (sourceB1650 + difference 5 2) sourceC1650) = raw14060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw14060; decide +kernel
    rw [ha]
    exact (canonical14060 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1650 + difference 3 0) (sourceB1650 + difference 0 3) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1650 + difference 3 0) (sourceB1650 + difference 0 3) sourceC1650) = raw24128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24128; decide +kernel
    rw [ha]
    exact (canonical24128 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1650 + difference 3 1) (sourceB1650 + difference 1 3) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1650 + difference 3 1) (sourceB1650 + difference 1 3) sourceC1650) = raw24129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24129; decide +kernel
    rw [ha]
    exact (canonical24129 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1650 + difference 3 2) (sourceB1650 + difference 2 3) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1650 + difference 3 2) (sourceB1650 + difference 2 3) sourceC1650) = raw24130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24130; decide +kernel
    rw [ha]
    exact (canonical24130 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1650 + difference 3 4) (sourceB1650 + difference 4 3) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1650 + difference 3 4) (sourceB1650 + difference 4 3) sourceC1650) = raw24131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24131; decide +kernel
    rw [ha]
    exact (canonical24131 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1650 + difference 3 5) (sourceB1650 + difference 5 3) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1650 + difference 3 5) (sourceB1650 + difference 5 3) sourceC1650) = raw14064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw14064; decide +kernel
    rw [ha]
    exact (canonical14064 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1650 + difference 4 0) (sourceB1650 + difference 0 4) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1650 + difference 4 0) (sourceB1650 + difference 0 4) sourceC1650) = raw24132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24132; decide +kernel
    rw [ha]
    exact (canonical24132 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1650 + difference 4 1) (sourceB1650 + difference 1 4) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1650 + difference 4 1) (sourceB1650 + difference 1 4) sourceC1650) = raw24133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24133; decide +kernel
    rw [ha]
    exact (canonical24133 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1650 + difference 4 2) (sourceB1650 + difference 2 4) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1650 + difference 4 2) (sourceB1650 + difference 2 4) sourceC1650) = raw24134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw24134; decide +kernel
    rw [ha]
    exact (canonical24134 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1650 + difference 4 3) (sourceB1650 + difference 3 4) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1650 + difference 4 3) (sourceB1650 + difference 3 4) sourceC1650) = raw7980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw7980; decide +kernel
    rw [ha]
    exact (canonical7980 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1650 + difference 4 5) (sourceB1650 + difference 5 4) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1650 + difference 4 5) (sourceB1650 + difference 5 4) sourceC1650) = raw14069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw14069; decide +kernel
    rw [ha]
    exact (canonical14069 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1650 + difference 5 0) (sourceB1650 + difference 0 5) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4174) := by
    have ha : (tripleCharges (sourceA1650 + difference 5 0) (sourceB1650 + difference 0 5) sourceC1650) = raw20936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw20936; decide +kernel
    rw [ha]
    exact (canonical20936 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1650 + difference 5 1) (sourceB1650 + difference 1 5) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1650 + difference 5 1) (sourceB1650 + difference 1 5) sourceC1650) = raw20937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw20937; decide +kernel
    rw [ha]
    exact (canonical20937 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1650 + difference 5 2) (sourceB1650 + difference 2 5) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1650 + difference 5 2) (sourceB1650 + difference 2 5) sourceC1650) = raw20938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw20938; decide +kernel
    rw [ha]
    exact (canonical20938 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1650 + difference 5 3) (sourceB1650 + difference 3 5) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1650 + difference 5 3) (sourceB1650 + difference 3 5) sourceC1650) = raw4617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw4617; decide +kernel
    rw [ha]
    exact (canonical4617 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1650 + difference 5 4) (sourceB1650 + difference 4 5) sourceC1650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1650 + difference 5 4) (sourceB1650 + difference 4 5) sourceC1650) = raw4613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1650 sourceB1650 sourceC1650 difference raw4613; decide +kernel
    rw [ha]
    exact (canonical4613 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1650 sourceB1650 sourceC1650
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1650, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1651 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1651 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1651 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm1651 : Integer.Sparse Master := [(Sum.inr 600, 2), (Sum.inr 602, 1), (Sum.inr 608, 2), (Sum.inr 1126, 2), (Sum.inr 1128, 2), (Sum.inr 1134, 4), (Sum.inr 1236, 4), (Sum.inr 1239, 2), (Sum.inr 1246, 2), (Sum.inr 1299, 2), (Sum.inr 1301, 2), (Sum.inr 2959, 2), (Sum.inr 3101, 2), (Sum.inr 3122, 1)]

theorem sourceEq1651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1651 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1651 + difference 0 1) (sourceB1651 + difference 1 0) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2959) := by
    have ha : (tripleCharges (sourceA1651 + difference 0 1) (sourceB1651 + difference 1 0) sourceC1651) = raw7994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw7994; decide +kernel
    rw [ha]
    exact (canonical7994 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1651 + difference 0 2) (sourceB1651 + difference 2 0) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2959) := by
    have ha : (tripleCharges (sourceA1651 + difference 0 2) (sourceB1651 + difference 2 0) sourceC1651) = raw7995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw7995; decide +kernel
    rw [ha]
    exact (canonical7995 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1651 + difference 0 3) (sourceB1651 + difference 3 0) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA1651 + difference 0 3) (sourceB1651 + difference 3 0) sourceC1651) = raw2711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw2711; decide +kernel
    rw [ha]
    exact (canonical2711 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1651 + difference 0 4) (sourceB1651 + difference 4 0) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA1651 + difference 0 4) (sourceB1651 + difference 4 0) sourceC1651) = raw2706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw2706; decide +kernel
    rw [ha]
    exact (canonical2706 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1651 + difference 0 5) (sourceB1651 + difference 5 0) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA1651 + difference 0 5) (sourceB1651 + difference 5 0) sourceC1651) = raw7996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw7996; decide +kernel
    rw [ha]
    exact (canonical7996 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1651 + difference 1 0) (sourceB1651 + difference 0 1) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 600) := by
    have ha : (tripleCharges (sourceA1651 + difference 1 0) (sourceB1651 + difference 0 1) sourceC1651) = raw24135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24135; decide +kernel
    rw [ha]
    exact (canonical24135 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1651 + difference 1 2) (sourceB1651 + difference 2 1) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA1651 + difference 1 2) (sourceB1651 + difference 2 1) sourceC1651) = raw24136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24136; decide +kernel
    rw [ha]
    exact (canonical24136 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1651 + difference 1 3) (sourceB1651 + difference 3 1) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1651 + difference 1 3) (sourceB1651 + difference 3 1) sourceC1651) = raw7985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw7985; decide +kernel
    rw [ha]
    exact (canonical7985 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1651 + difference 1 4) (sourceB1651 + difference 4 1) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1651 + difference 1 4) (sourceB1651 + difference 4 1) sourceC1651) = raw24137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24137; decide +kernel
    rw [ha]
    exact (canonical24137 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1651 + difference 1 5) (sourceB1651 + difference 5 1) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1651 + difference 1 5) (sourceB1651 + difference 5 1) sourceC1651) = raw24138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24138; decide +kernel
    rw [ha]
    exact (canonical24138 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1651 + difference 2 0) (sourceB1651 + difference 0 2) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 600) := by
    have ha : (tripleCharges (sourceA1651 + difference 2 0) (sourceB1651 + difference 0 2) sourceC1651) = raw24139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24139; decide +kernel
    rw [ha]
    exact (canonical24139 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1651 + difference 2 1) (sourceB1651 + difference 1 2) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA1651 + difference 2 1) (sourceB1651 + difference 1 2) sourceC1651) = raw24140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24140; decide +kernel
    rw [ha]
    exact (canonical24140 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1651 + difference 2 3) (sourceB1651 + difference 3 2) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1651 + difference 2 3) (sourceB1651 + difference 3 2) sourceC1651) = raw7989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw7989; decide +kernel
    rw [ha]
    exact (canonical7989 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1651 + difference 2 4) (sourceB1651 + difference 4 2) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1651 + difference 2 4) (sourceB1651 + difference 4 2) sourceC1651) = raw24141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24141; decide +kernel
    rw [ha]
    exact (canonical24141 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1651 + difference 2 5) (sourceB1651 + difference 5 2) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1651 + difference 2 5) (sourceB1651 + difference 5 2) sourceC1651) = raw24142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24142; decide +kernel
    rw [ha]
    exact (canonical24142 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1651 + difference 3 0) (sourceB1651 + difference 0 3) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 608) := by
    have ha : (tripleCharges (sourceA1651 + difference 3 0) (sourceB1651 + difference 0 3) sourceC1651) = raw24143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24143; decide +kernel
    rw [ha]
    exact (canonical24143 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1651 + difference 3 1) (sourceB1651 + difference 1 3) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1651 + difference 3 1) (sourceB1651 + difference 1 3) sourceC1651) = raw24144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24144; decide +kernel
    rw [ha]
    exact (canonical24144 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1651 + difference 3 2) (sourceB1651 + difference 2 3) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1651 + difference 3 2) (sourceB1651 + difference 2 3) sourceC1651) = raw24145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24145; decide +kernel
    rw [ha]
    exact (canonical24145 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1651 + difference 3 4) (sourceB1651 + difference 4 3) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1651 + difference 3 4) (sourceB1651 + difference 4 3) sourceC1651) = raw24146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24146; decide +kernel
    rw [ha]
    exact (canonical24146 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1651 + difference 3 5) (sourceB1651 + difference 5 3) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1651 + difference 3 5) (sourceB1651 + difference 5 3) sourceC1651) = raw24147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24147; decide +kernel
    rw [ha]
    exact (canonical24147 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1651 + difference 4 0) (sourceB1651 + difference 0 4) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 608) := by
    have ha : (tripleCharges (sourceA1651 + difference 4 0) (sourceB1651 + difference 0 4) sourceC1651) = raw24148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24148; decide +kernel
    rw [ha]
    exact (canonical24148 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1651 + difference 4 1) (sourceB1651 + difference 1 4) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1651 + difference 4 1) (sourceB1651 + difference 1 4) sourceC1651) = raw24149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24149; decide +kernel
    rw [ha]
    exact (canonical24149 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1651 + difference 4 2) (sourceB1651 + difference 2 4) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1651 + difference 4 2) (sourceB1651 + difference 2 4) sourceC1651) = raw24150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24150; decide +kernel
    rw [ha]
    exact (canonical24150 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1651 + difference 4 3) (sourceB1651 + difference 3 4) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1651 + difference 4 3) (sourceB1651 + difference 3 4) sourceC1651) = raw7997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw7997; decide +kernel
    rw [ha]
    exact (canonical7997 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1651 + difference 4 5) (sourceB1651 + difference 5 4) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1651 + difference 4 5) (sourceB1651 + difference 5 4) sourceC1651) = raw24151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw24151; decide +kernel
    rw [ha]
    exact (canonical24151 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1651 + difference 5 0) (sourceB1651 + difference 0 5) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1651 + difference 5 0) (sourceB1651 + difference 0 5) sourceC1651) = raw20953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw20953; decide +kernel
    rw [ha]
    exact (canonical20953 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1651 + difference 5 1) (sourceB1651 + difference 1 5) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1651 + difference 5 1) (sourceB1651 + difference 1 5) sourceC1651) = raw20954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw20954; decide +kernel
    rw [ha]
    exact (canonical20954 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1651 + difference 5 2) (sourceB1651 + difference 2 5) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1651 + difference 5 2) (sourceB1651 + difference 2 5) sourceC1651) = raw20955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw20955; decide +kernel
    rw [ha]
    exact (canonical20955 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1651 + difference 5 3) (sourceB1651 + difference 3 5) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1651 + difference 5 3) (sourceB1651 + difference 3 5) sourceC1651) = raw4639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw4639; decide +kernel
    rw [ha]
    exact (canonical4639 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1651 + difference 5 4) (sourceB1651 + difference 4 5) sourceC1651) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1651 + difference 5 4) (sourceB1651 + difference 4 5) sourceC1651) = raw4635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1651 sourceB1651 sourceC1651 difference raw4635; decide +kernel
    rw [ha]
    exact (canonical4635 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1651 sourceB1651 sourceC1651
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1651, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1652 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1652 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1652 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1652 : Integer.Sparse Master := [(Sum.inr 4457, 2), (Sum.inr 4461, 2), (Sum.inr 4496, 1), (Sum.inr 4498, 2), (Sum.inr 4502, 1), (Sum.inr 4503, 2), (Sum.inr 4589, 2), (Sum.inr 4600, 2), (Sum.inr 4602, 4), (Sum.inr 4606, 2), (Sum.inr 4607, 4), (Sum.inr 4617, 2), (Sum.inr 4619, 2), (Sum.inr 4624, 2)]

theorem sourceEq1652 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1652 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1652 + difference 0 1) (sourceB1652 + difference 1 0) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1652 + difference 0 1) (sourceB1652 + difference 1 0) sourceC1652) = raw24152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24152; decide +kernel
    rw [ha]
    exact (canonical24152 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1652 + difference 0 2) (sourceB1652 + difference 2 0) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1652 + difference 0 2) (sourceB1652 + difference 2 0) sourceC1652) = raw24153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24153; decide +kernel
    rw [ha]
    exact (canonical24153 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1652 + difference 0 3) (sourceB1652 + difference 3 0) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1652 + difference 0 3) (sourceB1652 + difference 3 0) sourceC1652) = raw24154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24154; decide +kernel
    rw [ha]
    exact (canonical24154 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1652 + difference 0 4) (sourceB1652 + difference 4 0) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1652 + difference 0 4) (sourceB1652 + difference 4 0) sourceC1652) = raw24155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24155; decide +kernel
    rw [ha]
    exact (canonical24155 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1652 + difference 0 5) (sourceB1652 + difference 5 0) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1652 + difference 0 5) (sourceB1652 + difference 5 0) sourceC1652) = raw24156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24156; decide +kernel
    rw [ha]
    exact (canonical24156 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1652 + difference 1 0) (sourceB1652 + difference 0 1) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1652 + difference 1 0) (sourceB1652 + difference 0 1) sourceC1652) = raw24157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24157; decide +kernel
    rw [ha]
    exact (canonical24157 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1652 + difference 1 2) (sourceB1652 + difference 2 1) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1652 + difference 1 2) (sourceB1652 + difference 2 1) sourceC1652) = raw24158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24158; decide +kernel
    rw [ha]
    exact (canonical24158 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1652 + difference 1 3) (sourceB1652 + difference 3 1) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1652 + difference 1 3) (sourceB1652 + difference 3 1) sourceC1652) = raw24159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24159; decide +kernel
    rw [ha]
    exact (canonical24159 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1652 + difference 1 4) (sourceB1652 + difference 4 1) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1652 + difference 1 4) (sourceB1652 + difference 4 1) sourceC1652) = raw24160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24160; decide +kernel
    rw [ha]
    exact (canonical24160 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1652 + difference 1 5) (sourceB1652 + difference 5 1) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1652 + difference 1 5) (sourceB1652 + difference 5 1) sourceC1652) = raw24161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24161; decide +kernel
    rw [ha]
    exact (canonical24161 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1652 + difference 2 0) (sourceB1652 + difference 0 2) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1652 + difference 2 0) (sourceB1652 + difference 0 2) sourceC1652) = raw24162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24162; decide +kernel
    rw [ha]
    exact (canonical24162 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1652 + difference 2 1) (sourceB1652 + difference 1 2) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1652 + difference 2 1) (sourceB1652 + difference 1 2) sourceC1652) = raw24163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24163; decide +kernel
    rw [ha]
    exact (canonical24163 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1652 + difference 2 3) (sourceB1652 + difference 3 2) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1652 + difference 2 3) (sourceB1652 + difference 3 2) sourceC1652) = raw24164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24164; decide +kernel
    rw [ha]
    exact (canonical24164 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1652 + difference 2 4) (sourceB1652 + difference 4 2) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1652 + difference 2 4) (sourceB1652 + difference 4 2) sourceC1652) = raw24165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24165; decide +kernel
    rw [ha]
    exact (canonical24165 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1652 + difference 2 5) (sourceB1652 + difference 5 2) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1652 + difference 2 5) (sourceB1652 + difference 5 2) sourceC1652) = raw24166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24166; decide +kernel
    rw [ha]
    exact (canonical24166 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1652 + difference 3 0) (sourceB1652 + difference 0 3) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1652 + difference 3 0) (sourceB1652 + difference 0 3) sourceC1652) = raw24167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24167; decide +kernel
    rw [ha]
    exact (canonical24167 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1652 + difference 3 1) (sourceB1652 + difference 1 3) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1652 + difference 3 1) (sourceB1652 + difference 1 3) sourceC1652) = raw24168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24168; decide +kernel
    rw [ha]
    exact (canonical24168 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1652 + difference 3 2) (sourceB1652 + difference 2 3) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1652 + difference 3 2) (sourceB1652 + difference 2 3) sourceC1652) = raw24169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24169; decide +kernel
    rw [ha]
    exact (canonical24169 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1652 + difference 3 4) (sourceB1652 + difference 4 3) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1652 + difference 3 4) (sourceB1652 + difference 4 3) sourceC1652) = raw24170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24170; decide +kernel
    rw [ha]
    exact (canonical24170 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1652 + difference 3 5) (sourceB1652 + difference 5 3) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1652 + difference 3 5) (sourceB1652 + difference 5 3) sourceC1652) = raw24171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24171; decide +kernel
    rw [ha]
    exact (canonical24171 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1652 + difference 4 0) (sourceB1652 + difference 0 4) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1652 + difference 4 0) (sourceB1652 + difference 0 4) sourceC1652) = raw24172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24172; decide +kernel
    rw [ha]
    exact (canonical24172 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1652 + difference 4 1) (sourceB1652 + difference 1 4) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1652 + difference 4 1) (sourceB1652 + difference 1 4) sourceC1652) = raw24173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24173; decide +kernel
    rw [ha]
    exact (canonical24173 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1652 + difference 4 2) (sourceB1652 + difference 2 4) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1652 + difference 4 2) (sourceB1652 + difference 2 4) sourceC1652) = raw24174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24174; decide +kernel
    rw [ha]
    exact (canonical24174 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1652 + difference 4 3) (sourceB1652 + difference 3 4) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1652 + difference 4 3) (sourceB1652 + difference 3 4) sourceC1652) = raw24175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24175; decide +kernel
    rw [ha]
    exact (canonical24175 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1652 + difference 4 5) (sourceB1652 + difference 5 4) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1652 + difference 4 5) (sourceB1652 + difference 5 4) sourceC1652) = raw24176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24176; decide +kernel
    rw [ha]
    exact (canonical24176 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1652 + difference 5 0) (sourceB1652 + difference 0 5) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1652 + difference 5 0) (sourceB1652 + difference 0 5) sourceC1652) = raw24177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24177; decide +kernel
    rw [ha]
    exact (canonical24177 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1652 + difference 5 1) (sourceB1652 + difference 1 5) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1652 + difference 5 1) (sourceB1652 + difference 1 5) sourceC1652) = raw24178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24178; decide +kernel
    rw [ha]
    exact (canonical24178 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1652 + difference 5 2) (sourceB1652 + difference 2 5) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1652 + difference 5 2) (sourceB1652 + difference 2 5) sourceC1652) = raw24179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24179; decide +kernel
    rw [ha]
    exact (canonical24179 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1652 + difference 5 3) (sourceB1652 + difference 3 5) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1652 + difference 5 3) (sourceB1652 + difference 3 5) sourceC1652) = raw24180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24180; decide +kernel
    rw [ha]
    exact (canonical24180 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1652 + difference 5 4) (sourceB1652 + difference 4 5) sourceC1652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1652 + difference 5 4) (sourceB1652 + difference 4 5) sourceC1652) = raw24181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1652 sourceB1652 sourceC1652 difference raw24181; decide +kernel
    rw [ha]
    exact (canonical24181 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1652 sourceB1652 sourceC1652
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1652, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1653 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1653 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1653 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1653 : Integer.Sparse Master := [(Sum.inr 1044, 2), (Sum.inr 1086, 1), (Sum.inr 1087, 2), (Sum.inr 1216, 2), (Sum.inr 1240, 2), (Sum.inr 1241, 4), (Sum.inr 1267, 4), (Sum.inr 1270, 2), (Sum.inr 1301, 2), (Sum.inr 1302, 2), (Sum.inr 1306, 2), (Sum.inr 1414, 2), (Sum.inr 1448, 2), (Sum.inr 1451, 1)]

theorem sourceEq1653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1653 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1653 + difference 0 1) (sourceB1653 + difference 1 0) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1653 + difference 0 1) (sourceB1653 + difference 1 0) sourceC1653) = raw24182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24182; decide +kernel
    rw [ha]
    exact (canonical24182 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1653 + difference 0 2) (sourceB1653 + difference 2 0) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1653 + difference 0 2) (sourceB1653 + difference 2 0) sourceC1653) = raw24183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24183; decide +kernel
    rw [ha]
    exact (canonical24183 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1653 + difference 0 3) (sourceB1653 + difference 3 0) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1653 + difference 0 3) (sourceB1653 + difference 3 0) sourceC1653) = raw24184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24184; decide +kernel
    rw [ha]
    exact (canonical24184 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1653 + difference 0 4) (sourceB1653 + difference 4 0) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1653 + difference 0 4) (sourceB1653 + difference 4 0) sourceC1653) = raw24185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24185; decide +kernel
    rw [ha]
    exact (canonical24185 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1653 + difference 0 5) (sourceB1653 + difference 5 0) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1653 + difference 0 5) (sourceB1653 + difference 5 0) sourceC1653) = raw24186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24186; decide +kernel
    rw [ha]
    exact (canonical24186 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1653 + difference 1 0) (sourceB1653 + difference 0 1) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1653 + difference 1 0) (sourceB1653 + difference 0 1) sourceC1653) = raw24187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24187; decide +kernel
    rw [ha]
    exact (canonical24187 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1653 + difference 1 2) (sourceB1653 + difference 2 1) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1653 + difference 1 2) (sourceB1653 + difference 2 1) sourceC1653) = raw24188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24188; decide +kernel
    rw [ha]
    exact (canonical24188 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1653 + difference 1 3) (sourceB1653 + difference 3 1) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1653 + difference 1 3) (sourceB1653 + difference 3 1) sourceC1653) = raw24189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24189; decide +kernel
    rw [ha]
    exact (canonical24189 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1653 + difference 1 4) (sourceB1653 + difference 4 1) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1653 + difference 1 4) (sourceB1653 + difference 4 1) sourceC1653) = raw24190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24190; decide +kernel
    rw [ha]
    exact (canonical24190 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1653 + difference 1 5) (sourceB1653 + difference 5 1) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1653 + difference 1 5) (sourceB1653 + difference 5 1) sourceC1653) = raw24191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24191; decide +kernel
    rw [ha]
    exact (canonical24191 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1653 + difference 2 0) (sourceB1653 + difference 0 2) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1653 + difference 2 0) (sourceB1653 + difference 0 2) sourceC1653) = raw24192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24192; decide +kernel
    rw [ha]
    exact (canonical24192 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1653 + difference 2 1) (sourceB1653 + difference 1 2) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1653 + difference 2 1) (sourceB1653 + difference 1 2) sourceC1653) = raw24193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24193; decide +kernel
    rw [ha]
    exact (canonical24193 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1653 + difference 2 3) (sourceB1653 + difference 3 2) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1653 + difference 2 3) (sourceB1653 + difference 3 2) sourceC1653) = raw24194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24194; decide +kernel
    rw [ha]
    exact (canonical24194 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1653 + difference 2 4) (sourceB1653 + difference 4 2) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1653 + difference 2 4) (sourceB1653 + difference 4 2) sourceC1653) = raw24195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24195; decide +kernel
    rw [ha]
    exact (canonical24195 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1653 + difference 2 5) (sourceB1653 + difference 5 2) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1653 + difference 2 5) (sourceB1653 + difference 5 2) sourceC1653) = raw24196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24196; decide +kernel
    rw [ha]
    exact (canonical24196 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1653 + difference 3 0) (sourceB1653 + difference 0 3) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1448) := by
    have ha : (tripleCharges (sourceA1653 + difference 3 0) (sourceB1653 + difference 0 3) sourceC1653) = raw24197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24197; decide +kernel
    rw [ha]
    exact (canonical24197 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1653 + difference 3 1) (sourceB1653 + difference 1 3) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1653 + difference 3 1) (sourceB1653 + difference 1 3) sourceC1653) = raw24198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24198; decide +kernel
    rw [ha]
    exact (canonical24198 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1653 + difference 3 2) (sourceB1653 + difference 2 3) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1653 + difference 3 2) (sourceB1653 + difference 2 3) sourceC1653) = raw24199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24199; decide +kernel
    rw [ha]
    exact (canonical24199 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1653 + difference 3 4) (sourceB1653 + difference 4 3) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1302) := by
    have ha : (tripleCharges (sourceA1653 + difference 3 4) (sourceB1653 + difference 4 3) sourceC1653) = raw24200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24200; decide +kernel
    rw [ha]
    exact (canonical24200 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1653 + difference 3 5) (sourceB1653 + difference 5 3) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1653 + difference 3 5) (sourceB1653 + difference 5 3) sourceC1653) = raw24201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24201; decide +kernel
    rw [ha]
    exact (canonical24201 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1653 + difference 4 0) (sourceB1653 + difference 0 4) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1448) := by
    have ha : (tripleCharges (sourceA1653 + difference 4 0) (sourceB1653 + difference 0 4) sourceC1653) = raw24202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24202; decide +kernel
    rw [ha]
    exact (canonical24202 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1653 + difference 4 1) (sourceB1653 + difference 1 4) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1653 + difference 4 1) (sourceB1653 + difference 1 4) sourceC1653) = raw24203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24203; decide +kernel
    rw [ha]
    exact (canonical24203 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1653 + difference 4 2) (sourceB1653 + difference 2 4) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1653 + difference 4 2) (sourceB1653 + difference 2 4) sourceC1653) = raw24204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24204; decide +kernel
    rw [ha]
    exact (canonical24204 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1653 + difference 4 3) (sourceB1653 + difference 3 4) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1302) := by
    have ha : (tripleCharges (sourceA1653 + difference 4 3) (sourceB1653 + difference 3 4) sourceC1653) = raw24205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24205; decide +kernel
    rw [ha]
    exact (canonical24205 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1653 + difference 4 5) (sourceB1653 + difference 5 4) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1653 + difference 4 5) (sourceB1653 + difference 5 4) sourceC1653) = raw24206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24206; decide +kernel
    rw [ha]
    exact (canonical24206 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1653 + difference 5 0) (sourceB1653 + difference 0 5) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1451) := by
    have ha : (tripleCharges (sourceA1653 + difference 5 0) (sourceB1653 + difference 0 5) sourceC1653) = raw24207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24207; decide +kernel
    rw [ha]
    exact (canonical24207 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1653 + difference 5 1) (sourceB1653 + difference 1 5) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1653 + difference 5 1) (sourceB1653 + difference 1 5) sourceC1653) = raw24208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24208; decide +kernel
    rw [ha]
    exact (canonical24208 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1653 + difference 5 2) (sourceB1653 + difference 2 5) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1653 + difference 5 2) (sourceB1653 + difference 2 5) sourceC1653) = raw24209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24209; decide +kernel
    rw [ha]
    exact (canonical24209 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1653 + difference 5 3) (sourceB1653 + difference 3 5) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1653 + difference 5 3) (sourceB1653 + difference 3 5) sourceC1653) = raw24210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24210; decide +kernel
    rw [ha]
    exact (canonical24210 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1653 + difference 5 4) (sourceB1653 + difference 4 5) sourceC1653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1653 + difference 5 4) (sourceB1653 + difference 4 5) sourceC1653) = raw24211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1653 sourceB1653 sourceC1653 difference raw24211; decide +kernel
    rw [ha]
    exact (canonical24211 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1653 sourceB1653 sourceC1653
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1653, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1654 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1654 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1654 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1654 : Integer.Sparse Master := [(Sum.inr 1737, 2), (Sum.inr 1739, 2), (Sum.inr 1753, 1), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

theorem sourceEq1654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1654 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 0) (sourceB1654 + difference 0 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 0) (sourceB1654 + difference 0 0) sourceC1654) = raw23947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw23947; decide +kernel
    rw [ha]
    exact (canonical23947 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 1) (sourceB1654 + difference 1 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 1) (sourceB1654 + difference 1 0) sourceC1654) = raw23942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw23942; decide +kernel
    rw [ha]
    exact (canonical23942 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 2) (sourceB1654 + difference 2 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 2) (sourceB1654 + difference 2 0) sourceC1654) = raw24212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw24212; decide +kernel
    rw [ha]
    exact (canonical24212 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 3) (sourceB1654 + difference 3 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 3) (sourceB1654 + difference 3 0) sourceC1654) = raw24081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw24081; decide +kernel
    rw [ha]
    exact (canonical24081 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 4) (sourceB1654 + difference 4 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 4) (sourceB1654 + difference 4 0) sourceC1654) = raw24213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw24213; decide +kernel
    rw [ha]
    exact (canonical24213 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 5) (sourceB1654 + difference 5 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1753) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 5) (sourceB1654 + difference 5 0) sourceC1654) = raw24214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw24214; decide +kernel
    rw [ha]
    exact (canonical24214 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1654 + sourceB1654) sourceC1654) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1654 + sourceB1654) sourceC1654) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1654 sourceB1654 sourceC1654 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1654 sourceB1654 sourceC1654
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1654, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1655 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1655 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1655 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1655 : Integer.Sparse Master := [(Sum.inr 1727, 1), (Sum.inr 3293, 2), (Sum.inr 3305, 1), (Sum.inr 3308, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

theorem sourceEq1655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1655 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 0) (sourceB1655 + difference 0 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 0) (sourceB1655 + difference 0 3) sourceC1655) = raw24215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw24215; decide +kernel
    rw [ha]
    exact (canonical24215 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 1) (sourceB1655 + difference 1 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 1) (sourceB1655 + difference 1 3) sourceC1655) = raw23952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw23952; decide +kernel
    rw [ha]
    exact (canonical23952 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 2) (sourceB1655 + difference 2 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 2) (sourceB1655 + difference 2 3) sourceC1655) = raw24216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw24216; decide +kernel
    rw [ha]
    exact (canonical24216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 3) (sourceB1655 + difference 3 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 3) (sourceB1655 + difference 3 3) sourceC1655) = raw23947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw23947; decide +kernel
    rw [ha]
    exact (canonical23947 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 4) (sourceB1655 + difference 4 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 4) (sourceB1655 + difference 4 3) sourceC1655) = raw24217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw24217; decide +kernel
    rw [ha]
    exact (canonical24217 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 5) (sourceB1655 + difference 5 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3309) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 5) (sourceB1655 + difference 5 3) sourceC1655) = raw24218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw24218; decide +kernel
    rw [ha]
    exact (canonical24218 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1655 + sourceB1655) sourceC1655) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1655 + sourceB1655) sourceC1655) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1655 sourceB1655 sourceC1655 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1655 sourceB1655 sourceC1655
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1655, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1656 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1656 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1656 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1656 : Integer.Sparse Master := [(Sum.inr 4175, 2), (Sum.inr 4177, 1), (Sum.inr 4180, 1), (Sum.inr 4186, 1), (Sum.inr 4544, 2), (Sum.inr 4546, 2), (Sum.inr 4549, 2), (Sum.inr 4554, 2), (Sum.inr 4606, 2), (Sum.inr 4608, 1), (Sum.inr 4612, 1), (Sum.inr 4622, 2), (Sum.inr 4623, 1), (Sum.inr 4624, 3), (Sum.inr 4625, 1), (Sum.inr 4628, 1), (Sum.inr 5169, 2), (Sum.inr 5293, 1), (Sum.inr 5307, 1), (Sum.inr 5309, 1)]

theorem sourceEq1656 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1656 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1656 + difference 0 1) (sourceB1656 + difference 1 0) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1656 + difference 0 1) (sourceB1656 + difference 1 0) sourceC1656) = raw10207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw10207; decide +kernel
    rw [ha]
    exact (canonical10207 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1656 + difference 0 2) (sourceB1656 + difference 2 0) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1656 + difference 0 2) (sourceB1656 + difference 2 0) sourceC1656) = raw10208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw10208; decide +kernel
    rw [ha]
    exact (canonical10208 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1656 + difference 0 3) (sourceB1656 + difference 3 0) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA1656 + difference 0 3) (sourceB1656 + difference 3 0) sourceC1656) = raw4306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw4306; decide +kernel
    rw [ha]
    exact (canonical4306 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1656 + difference 0 4) (sourceB1656 + difference 4 0) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1656 + difference 0 4) (sourceB1656 + difference 4 0) sourceC1656) = raw4301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw4301; decide +kernel
    rw [ha]
    exact (canonical4301 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1656 + difference 0 5) (sourceB1656 + difference 5 0) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA1656 + difference 0 5) (sourceB1656 + difference 5 0) sourceC1656) = raw10209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw10209; decide +kernel
    rw [ha]
    exact (canonical10209 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1656 + difference 1 0) (sourceB1656 + difference 0 1) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1656 + difference 1 0) (sourceB1656 + difference 0 1) sourceC1656) = raw24219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24219; decide +kernel
    rw [ha]
    exact (canonical24219 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1656 + difference 1 2) (sourceB1656 + difference 2 1) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1656 + difference 1 2) (sourceB1656 + difference 2 1) sourceC1656) = raw24220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24220; decide +kernel
    rw [ha]
    exact (canonical24220 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1656 + difference 1 3) (sourceB1656 + difference 3 1) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1656 + difference 1 3) (sourceB1656 + difference 3 1) sourceC1656) = raw10198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw10198; decide +kernel
    rw [ha]
    exact (canonical10198 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1656 + difference 1 4) (sourceB1656 + difference 4 1) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1656 + difference 1 4) (sourceB1656 + difference 4 1) sourceC1656) = raw24221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24221; decide +kernel
    rw [ha]
    exact (canonical24221 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1656 + difference 1 5) (sourceB1656 + difference 5 1) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1656 + difference 1 5) (sourceB1656 + difference 5 1) sourceC1656) = raw24222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24222; decide +kernel
    rw [ha]
    exact (canonical24222 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1656 + difference 2 0) (sourceB1656 + difference 0 2) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1656 + difference 2 0) (sourceB1656 + difference 0 2) sourceC1656) = raw24223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24223; decide +kernel
    rw [ha]
    exact (canonical24223 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1656 + difference 2 1) (sourceB1656 + difference 1 2) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1656 + difference 2 1) (sourceB1656 + difference 1 2) sourceC1656) = raw24224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24224; decide +kernel
    rw [ha]
    exact (canonical24224 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1656 + difference 2 3) (sourceB1656 + difference 3 2) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1656 + difference 2 3) (sourceB1656 + difference 3 2) sourceC1656) = raw10202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw10202; decide +kernel
    rw [ha]
    exact (canonical10202 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1656 + difference 2 4) (sourceB1656 + difference 4 2) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1656 + difference 2 4) (sourceB1656 + difference 4 2) sourceC1656) = raw24225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24225; decide +kernel
    rw [ha]
    exact (canonical24225 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1656 + difference 2 5) (sourceB1656 + difference 5 2) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1656 + difference 2 5) (sourceB1656 + difference 5 2) sourceC1656) = raw24226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24226; decide +kernel
    rw [ha]
    exact (canonical24226 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1656 + difference 3 0) (sourceB1656 + difference 0 3) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1656 + difference 3 0) (sourceB1656 + difference 0 3) sourceC1656) = raw24227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24227; decide +kernel
    rw [ha]
    exact (canonical24227 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1656 + difference 3 1) (sourceB1656 + difference 1 3) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1656 + difference 3 1) (sourceB1656 + difference 1 3) sourceC1656) = raw24228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24228; decide +kernel
    rw [ha]
    exact (canonical24228 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1656 + difference 3 2) (sourceB1656 + difference 2 3) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1656 + difference 3 2) (sourceB1656 + difference 2 3) sourceC1656) = raw24229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24229; decide +kernel
    rw [ha]
    exact (canonical24229 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1656 + difference 3 4) (sourceB1656 + difference 4 3) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1656 + difference 3 4) (sourceB1656 + difference 4 3) sourceC1656) = raw24230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24230; decide +kernel
    rw [ha]
    exact (canonical24230 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1656 + difference 3 5) (sourceB1656 + difference 5 3) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1656 + difference 3 5) (sourceB1656 + difference 5 3) sourceC1656) = raw24231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw24231; decide +kernel
    rw [ha]
    exact (canonical24231 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1656 + difference 4 0) (sourceB1656 + difference 0 4) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4186) := by
    have ha : (tripleCharges (sourceA1656 + difference 4 0) (sourceB1656 + difference 0 4) sourceC1656) = raw22577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw22577; decide +kernel
    rw [ha]
    exact (canonical22577 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1656 + difference 4 1) (sourceB1656 + difference 1 4) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA1656 + difference 4 1) (sourceB1656 + difference 1 4) sourceC1656) = raw22578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw22578; decide +kernel
    rw [ha]
    exact (canonical22578 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1656 + difference 4 2) (sourceB1656 + difference 2 4) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA1656 + difference 4 2) (sourceB1656 + difference 2 4) sourceC1656) = raw22579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw22579; decide +kernel
    rw [ha]
    exact (canonical22579 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1656 + difference 4 3) (sourceB1656 + difference 3 4) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4628) := by
    have ha : (tripleCharges (sourceA1656 + difference 4 3) (sourceB1656 + difference 3 4) sourceC1656) = raw10210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw10210; decide +kernel
    rw [ha]
    exact (canonical10210 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1656 + difference 4 5) (sourceB1656 + difference 5 4) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1656 + difference 4 5) (sourceB1656 + difference 5 4) sourceC1656) = raw22580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw22580; decide +kernel
    rw [ha]
    exact (canonical22580 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1656 + difference 5 0) (sourceB1656 + difference 0 5) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1656 + difference 5 0) (sourceB1656 + difference 0 5) sourceC1656) = raw20390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw20390; decide +kernel
    rw [ha]
    exact (canonical20390 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1656 + difference 5 1) (sourceB1656 + difference 1 5) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1656 + difference 5 1) (sourceB1656 + difference 1 5) sourceC1656) = raw20391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw20391; decide +kernel
    rw [ha]
    exact (canonical20391 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1656 + difference 5 2) (sourceB1656 + difference 2 5) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1656 + difference 5 2) (sourceB1656 + difference 2 5) sourceC1656) = raw20392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw20392; decide +kernel
    rw [ha]
    exact (canonical20392 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1656 + difference 5 3) (sourceB1656 + difference 3 5) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1656 + difference 5 3) (sourceB1656 + difference 3 5) sourceC1656) = raw4302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw4302; decide +kernel
    rw [ha]
    exact (canonical4302 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1656 + difference 5 4) (sourceB1656 + difference 4 5) sourceC1656) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1656 + difference 5 4) (sourceB1656 + difference 4 5) sourceC1656) = raw4297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1656 sourceB1656 sourceC1656 difference raw4297; decide +kernel
    rw [ha]
    exact (canonical4297 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1656 sourceB1656 sourceC1656
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1656, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1657 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1657 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1657 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1657 : Integer.Sparse Master := [(Sum.inr 603, 2), (Sum.inr 605, 1), (Sum.inr 608, 1), (Sum.inr 614, 1), (Sum.inr 1129, 2), (Sum.inr 1131, 2), (Sum.inr 1134, 2), (Sum.inr 1139, 2), (Sum.inr 1240, 2), (Sum.inr 1242, 1), (Sum.inr 1246, 1), (Sum.inr 1299, 2), (Sum.inr 1300, 1), (Sum.inr 1301, 3), (Sum.inr 1304, 1), (Sum.inr 1312, 1), (Sum.inr 2960, 2), (Sum.inr 3102, 1), (Sum.inr 3122, 1), (Sum.inr 3123, 1)]

theorem sourceEq1657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1657 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1657 + difference 0 1) (sourceB1657 + difference 1 0) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA1657 + difference 0 1) (sourceB1657 + difference 1 0) sourceC1657) = raw24232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24232; decide +kernel
    rw [ha]
    exact (canonical24232 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1657 + difference 0 2) (sourceB1657 + difference 2 0) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA1657 + difference 0 2) (sourceB1657 + difference 2 0) sourceC1657) = raw24233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24233; decide +kernel
    rw [ha]
    exact (canonical24233 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1657 + difference 0 3) (sourceB1657 + difference 3 0) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA1657 + difference 0 3) (sourceB1657 + difference 3 0) sourceC1657) = raw4336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw4336; decide +kernel
    rw [ha]
    exact (canonical4336 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1657 + difference 0 4) (sourceB1657 + difference 4 0) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA1657 + difference 0 4) (sourceB1657 + difference 4 0) sourceC1657) = raw4331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw4331; decide +kernel
    rw [ha]
    exact (canonical4331 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1657 + difference 0 5) (sourceB1657 + difference 5 0) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA1657 + difference 0 5) (sourceB1657 + difference 5 0) sourceC1657) = raw24234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24234; decide +kernel
    rw [ha]
    exact (canonical24234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1657 + difference 1 0) (sourceB1657 + difference 0 1) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 603) := by
    have ha : (tripleCharges (sourceA1657 + difference 1 0) (sourceB1657 + difference 0 1) sourceC1657) = raw24235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24235; decide +kernel
    rw [ha]
    exact (canonical24235 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1657 + difference 1 2) (sourceB1657 + difference 2 1) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1129) := by
    have ha : (tripleCharges (sourceA1657 + difference 1 2) (sourceB1657 + difference 2 1) sourceC1657) = raw24236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24236; decide +kernel
    rw [ha]
    exact (canonical24236 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1657 + difference 1 3) (sourceB1657 + difference 3 1) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1657 + difference 1 3) (sourceB1657 + difference 3 1) sourceC1657) = raw20400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw20400; decide +kernel
    rw [ha]
    exact (canonical20400 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1657 + difference 1 4) (sourceB1657 + difference 4 1) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1657 + difference 1 4) (sourceB1657 + difference 4 1) sourceC1657) = raw24237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24237; decide +kernel
    rw [ha]
    exact (canonical24237 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1657 + difference 1 5) (sourceB1657 + difference 5 1) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1657 + difference 1 5) (sourceB1657 + difference 5 1) sourceC1657) = raw24238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24238; decide +kernel
    rw [ha]
    exact (canonical24238 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1657 + difference 2 0) (sourceB1657 + difference 0 2) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 603) := by
    have ha : (tripleCharges (sourceA1657 + difference 2 0) (sourceB1657 + difference 0 2) sourceC1657) = raw24239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24239; decide +kernel
    rw [ha]
    exact (canonical24239 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1657 + difference 2 1) (sourceB1657 + difference 1 2) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1129) := by
    have ha : (tripleCharges (sourceA1657 + difference 2 1) (sourceB1657 + difference 1 2) sourceC1657) = raw24240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24240; decide +kernel
    rw [ha]
    exact (canonical24240 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1657 + difference 2 3) (sourceB1657 + difference 3 2) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1657 + difference 2 3) (sourceB1657 + difference 3 2) sourceC1657) = raw20404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw20404; decide +kernel
    rw [ha]
    exact (canonical20404 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1657 + difference 2 4) (sourceB1657 + difference 4 2) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1657 + difference 2 4) (sourceB1657 + difference 4 2) sourceC1657) = raw24241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24241; decide +kernel
    rw [ha]
    exact (canonical24241 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1657 + difference 2 5) (sourceB1657 + difference 5 2) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1657 + difference 2 5) (sourceB1657 + difference 5 2) sourceC1657) = raw24242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24242; decide +kernel
    rw [ha]
    exact (canonical24242 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1657 + difference 3 0) (sourceB1657 + difference 0 3) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 608) := by
    have ha : (tripleCharges (sourceA1657 + difference 3 0) (sourceB1657 + difference 0 3) sourceC1657) = raw24243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24243; decide +kernel
    rw [ha]
    exact (canonical24243 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1657 + difference 3 1) (sourceB1657 + difference 1 3) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1657 + difference 3 1) (sourceB1657 + difference 1 3) sourceC1657) = raw24244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24244; decide +kernel
    rw [ha]
    exact (canonical24244 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1657 + difference 3 2) (sourceB1657 + difference 2 3) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1657 + difference 3 2) (sourceB1657 + difference 2 3) sourceC1657) = raw24245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24245; decide +kernel
    rw [ha]
    exact (canonical24245 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1657 + difference 3 4) (sourceB1657 + difference 4 3) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1657 + difference 3 4) (sourceB1657 + difference 4 3) sourceC1657) = raw24246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24246; decide +kernel
    rw [ha]
    exact (canonical24246 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1657 + difference 3 5) (sourceB1657 + difference 5 3) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1300) := by
    have ha : (tripleCharges (sourceA1657 + difference 3 5) (sourceB1657 + difference 5 3) sourceC1657) = raw24247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw24247; decide +kernel
    rw [ha]
    exact (canonical24247 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1657 + difference 4 0) (sourceB1657 + difference 0 4) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 614) := by
    have ha : (tripleCharges (sourceA1657 + difference 4 0) (sourceB1657 + difference 0 4) sourceC1657) = raw22598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw22598; decide +kernel
    rw [ha]
    exact (canonical22598 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1657 + difference 4 1) (sourceB1657 + difference 1 4) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1657 + difference 4 1) (sourceB1657 + difference 1 4) sourceC1657) = raw22599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw22599; decide +kernel
    rw [ha]
    exact (canonical22599 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1657 + difference 4 2) (sourceB1657 + difference 2 4) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1657 + difference 4 2) (sourceB1657 + difference 2 4) sourceC1657) = raw22600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw22600; decide +kernel
    rw [ha]
    exact (canonical22600 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1657 + difference 4 3) (sourceB1657 + difference 3 4) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1312) := by
    have ha : (tripleCharges (sourceA1657 + difference 4 3) (sourceB1657 + difference 3 4) sourceC1657) = raw20413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw20413; decide +kernel
    rw [ha]
    exact (canonical20413 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1657 + difference 4 5) (sourceB1657 + difference 5 4) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1657 + difference 4 5) (sourceB1657 + difference 5 4) sourceC1657) = raw22601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw22601; decide +kernel
    rw [ha]
    exact (canonical22601 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1657 + difference 5 0) (sourceB1657 + difference 0 5) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 605) := by
    have ha : (tripleCharges (sourceA1657 + difference 5 0) (sourceB1657 + difference 0 5) sourceC1657) = raw20405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw20405; decide +kernel
    rw [ha]
    exact (canonical20405 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1657 + difference 5 1) (sourceB1657 + difference 1 5) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1657 + difference 5 1) (sourceB1657 + difference 1 5) sourceC1657) = raw20406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw20406; decide +kernel
    rw [ha]
    exact (canonical20406 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1657 + difference 5 2) (sourceB1657 + difference 2 5) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1657 + difference 5 2) (sourceB1657 + difference 2 5) sourceC1657) = raw20407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw20407; decide +kernel
    rw [ha]
    exact (canonical20407 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1657 + difference 5 3) (sourceB1657 + difference 3 5) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA1657 + difference 5 3) (sourceB1657 + difference 3 5) sourceC1657) = raw4332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw4332; decide +kernel
    rw [ha]
    exact (canonical4332 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1657 + difference 5 4) (sourceB1657 + difference 4 5) sourceC1657) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1657 + difference 5 4) (sourceB1657 + difference 4 5) sourceC1657) = raw4327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1657 sourceB1657 sourceC1657 difference raw4327; decide +kernel
    rw [ha]
    exact (canonical4327 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1657 sourceB1657 sourceC1657
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1657, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1658 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1658 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1658 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1658 : Integer.Sparse Master := [(Sum.inr 4458, 4), (Sum.inr 4498, 2), (Sum.inr 4499, 2), (Sum.inr 4502, 2), (Sum.inr 4590, 2), (Sum.inr 4602, 4), (Sum.inr 4603, 4), (Sum.inr 4606, 4), (Sum.inr 4619, 2), (Sum.inr 4620, 1), (Sum.inr 4623, 2), (Sum.inr 4624, 1)]

theorem sourceEq1658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1658 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1658 + difference 0 1) (sourceB1658 + difference 1 0) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1658 + difference 0 1) (sourceB1658 + difference 1 0) sourceC1658) = raw24248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24248; decide +kernel
    rw [ha]
    exact (canonical24248 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1658 + difference 0 2) (sourceB1658 + difference 2 0) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1658 + difference 0 2) (sourceB1658 + difference 2 0) sourceC1658) = raw24249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24249; decide +kernel
    rw [ha]
    exact (canonical24249 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1658 + difference 0 3) (sourceB1658 + difference 3 0) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1658 + difference 0 3) (sourceB1658 + difference 3 0) sourceC1658) = raw24250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24250; decide +kernel
    rw [ha]
    exact (canonical24250 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1658 + difference 0 4) (sourceB1658 + difference 4 0) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1658 + difference 0 4) (sourceB1658 + difference 4 0) sourceC1658) = raw24156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24156; decide +kernel
    rw [ha]
    exact (canonical24156 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1658 + difference 0 5) (sourceB1658 + difference 5 0) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1658 + difference 0 5) (sourceB1658 + difference 5 0) sourceC1658) = raw24251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24251; decide +kernel
    rw [ha]
    exact (canonical24251 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1658 + difference 1 0) (sourceB1658 + difference 0 1) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1658 + difference 1 0) (sourceB1658 + difference 0 1) sourceC1658) = raw24252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24252; decide +kernel
    rw [ha]
    exact (canonical24252 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1658 + difference 1 2) (sourceB1658 + difference 2 1) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1658 + difference 1 2) (sourceB1658 + difference 2 1) sourceC1658) = raw24253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24253; decide +kernel
    rw [ha]
    exact (canonical24253 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1658 + difference 1 3) (sourceB1658 + difference 3 1) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1658 + difference 1 3) (sourceB1658 + difference 3 1) sourceC1658) = raw24254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24254; decide +kernel
    rw [ha]
    exact (canonical24254 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1658 + difference 1 4) (sourceB1658 + difference 4 1) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1658 + difference 1 4) (sourceB1658 + difference 4 1) sourceC1658) = raw24161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24161; decide +kernel
    rw [ha]
    exact (canonical24161 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1658 + difference 1 5) (sourceB1658 + difference 5 1) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1658 + difference 1 5) (sourceB1658 + difference 5 1) sourceC1658) = raw24255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24255; decide +kernel
    rw [ha]
    exact (canonical24255 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1658 + difference 2 0) (sourceB1658 + difference 0 2) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1658 + difference 2 0) (sourceB1658 + difference 0 2) sourceC1658) = raw24256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24256; decide +kernel
    rw [ha]
    exact (canonical24256 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1658 + difference 2 1) (sourceB1658 + difference 1 2) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1658 + difference 2 1) (sourceB1658 + difference 1 2) sourceC1658) = raw24257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24257; decide +kernel
    rw [ha]
    exact (canonical24257 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1658 + difference 2 3) (sourceB1658 + difference 3 2) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1658 + difference 2 3) (sourceB1658 + difference 3 2) sourceC1658) = raw24258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24258; decide +kernel
    rw [ha]
    exact (canonical24258 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1658 + difference 2 4) (sourceB1658 + difference 4 2) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1658 + difference 2 4) (sourceB1658 + difference 4 2) sourceC1658) = raw24166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24166; decide +kernel
    rw [ha]
    exact (canonical24166 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1658 + difference 2 5) (sourceB1658 + difference 5 2) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1658 + difference 2 5) (sourceB1658 + difference 5 2) sourceC1658) = raw24259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24259; decide +kernel
    rw [ha]
    exact (canonical24259 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1658 + difference 3 0) (sourceB1658 + difference 0 3) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1658 + difference 3 0) (sourceB1658 + difference 0 3) sourceC1658) = raw24260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24260; decide +kernel
    rw [ha]
    exact (canonical24260 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1658 + difference 3 1) (sourceB1658 + difference 1 3) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1658 + difference 3 1) (sourceB1658 + difference 1 3) sourceC1658) = raw24261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24261; decide +kernel
    rw [ha]
    exact (canonical24261 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1658 + difference 3 2) (sourceB1658 + difference 2 3) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1658 + difference 3 2) (sourceB1658 + difference 2 3) sourceC1658) = raw24262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24262; decide +kernel
    rw [ha]
    exact (canonical24262 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1658 + difference 3 4) (sourceB1658 + difference 4 3) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1658 + difference 3 4) (sourceB1658 + difference 4 3) sourceC1658) = raw24171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24171; decide +kernel
    rw [ha]
    exact (canonical24171 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1658 + difference 3 5) (sourceB1658 + difference 5 3) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1658 + difference 3 5) (sourceB1658 + difference 5 3) sourceC1658) = raw24263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24263; decide +kernel
    rw [ha]
    exact (canonical24263 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1658 + difference 4 0) (sourceB1658 + difference 0 4) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1658 + difference 4 0) (sourceB1658 + difference 0 4) sourceC1658) = raw24264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24264; decide +kernel
    rw [ha]
    exact (canonical24264 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1658 + difference 4 1) (sourceB1658 + difference 1 4) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1658 + difference 4 1) (sourceB1658 + difference 1 4) sourceC1658) = raw24265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24265; decide +kernel
    rw [ha]
    exact (canonical24265 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1658 + difference 4 2) (sourceB1658 + difference 2 4) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1658 + difference 4 2) (sourceB1658 + difference 2 4) sourceC1658) = raw24266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24266; decide +kernel
    rw [ha]
    exact (canonical24266 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1658 + difference 4 3) (sourceB1658 + difference 3 4) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4620) := by
    have ha : (tripleCharges (sourceA1658 + difference 4 3) (sourceB1658 + difference 3 4) sourceC1658) = raw24267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24267; decide +kernel
    rw [ha]
    exact (canonical24267 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1658 + difference 4 5) (sourceB1658 + difference 5 4) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1658 + difference 4 5) (sourceB1658 + difference 5 4) sourceC1658) = raw24268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24268; decide +kernel
    rw [ha]
    exact (canonical24268 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1658 + difference 5 0) (sourceB1658 + difference 0 5) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1658 + difference 5 0) (sourceB1658 + difference 0 5) sourceC1658) = raw24172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24172; decide +kernel
    rw [ha]
    exact (canonical24172 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1658 + difference 5 1) (sourceB1658 + difference 1 5) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1658 + difference 5 1) (sourceB1658 + difference 1 5) sourceC1658) = raw24173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24173; decide +kernel
    rw [ha]
    exact (canonical24173 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1658 + difference 5 2) (sourceB1658 + difference 2 5) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1658 + difference 5 2) (sourceB1658 + difference 2 5) sourceC1658) = raw24174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24174; decide +kernel
    rw [ha]
    exact (canonical24174 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1658 + difference 5 3) (sourceB1658 + difference 3 5) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1658 + difference 5 3) (sourceB1658 + difference 3 5) sourceC1658) = raw24175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24175; decide +kernel
    rw [ha]
    exact (canonical24175 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1658 + difference 5 4) (sourceB1658 + difference 4 5) sourceC1658) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1658 + difference 5 4) (sourceB1658 + difference 4 5) sourceC1658) = raw24269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1658 sourceB1658 sourceC1658 difference raw24269; decide +kernel
    rw [ha]
    exact (canonical24269 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1658 sourceB1658 sourceC1658
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1658, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1659 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1659 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1659 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm1659 : Integer.Sparse Master := [(Sum.inr 4165, 2), (Sum.inr 4166, 1), (Sum.inr 4167, 1), (Sum.inr 4185, 1), (Sum.inr 4537, 2), (Sum.inr 4538, 2), (Sum.inr 4539, 2), (Sum.inr 4553, 2), (Sum.inr 4570, 2), (Sum.inr 4572, 1), (Sum.inr 4575, 1), (Sum.inr 4618, 2), (Sum.inr 4619, 3), (Sum.inr 4621, 1), (Sum.inr 4623, 1), (Sum.inr 4627, 1), (Sum.inr 5170, 2), (Sum.inr 5302, 1), (Sum.inr 5306, 1), (Sum.inr 5310, 1)]

theorem sourceEq1659 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1659 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1659 + difference 0 1) (sourceB1659 + difference 1 0) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA1659 + difference 0 1) (sourceB1659 + difference 1 0) sourceC1659) = raw7567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw7567; decide +kernel
    rw [ha]
    exact (canonical7567 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1659 + difference 0 2) (sourceB1659 + difference 2 0) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA1659 + difference 0 2) (sourceB1659 + difference 2 0) sourceC1659) = raw7568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw7568; decide +kernel
    rw [ha]
    exact (canonical7568 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1659 + difference 0 3) (sourceB1659 + difference 3 0) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA1659 + difference 0 3) (sourceB1659 + difference 3 0) sourceC1659) = raw2651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw2651; decide +kernel
    rw [ha]
    exact (canonical2651 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1659 + difference 0 4) (sourceB1659 + difference 4 0) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA1659 + difference 0 4) (sourceB1659 + difference 4 0) sourceC1659) = raw2646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw2646; decide +kernel
    rw [ha]
    exact (canonical2646 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1659 + difference 0 5) (sourceB1659 + difference 5 0) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA1659 + difference 0 5) (sourceB1659 + difference 5 0) sourceC1659) = raw7569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw7569; decide +kernel
    rw [ha]
    exact (canonical7569 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1659 + difference 1 0) (sourceB1659 + difference 0 1) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4165) := by
    have ha : (tripleCharges (sourceA1659 + difference 1 0) (sourceB1659 + difference 0 1) sourceC1659) = raw24270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24270; decide +kernel
    rw [ha]
    exact (canonical24270 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1659 + difference 1 2) (sourceB1659 + difference 2 1) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4537) := by
    have ha : (tripleCharges (sourceA1659 + difference 1 2) (sourceB1659 + difference 2 1) sourceC1659) = raw24271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24271; decide +kernel
    rw [ha]
    exact (canonical24271 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1659 + difference 1 3) (sourceB1659 + difference 3 1) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1659 + difference 1 3) (sourceB1659 + difference 3 1) sourceC1659) = raw7558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw7558; decide +kernel
    rw [ha]
    exact (canonical7558 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1659 + difference 1 4) (sourceB1659 + difference 4 1) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA1659 + difference 1 4) (sourceB1659 + difference 4 1) sourceC1659) = raw24272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24272; decide +kernel
    rw [ha]
    exact (canonical24272 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1659 + difference 1 5) (sourceB1659 + difference 5 1) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1659 + difference 1 5) (sourceB1659 + difference 5 1) sourceC1659) = raw24273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24273; decide +kernel
    rw [ha]
    exact (canonical24273 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1659 + difference 2 0) (sourceB1659 + difference 0 2) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4165) := by
    have ha : (tripleCharges (sourceA1659 + difference 2 0) (sourceB1659 + difference 0 2) sourceC1659) = raw24274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24274; decide +kernel
    rw [ha]
    exact (canonical24274 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1659 + difference 2 1) (sourceB1659 + difference 1 2) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4537) := by
    have ha : (tripleCharges (sourceA1659 + difference 2 1) (sourceB1659 + difference 1 2) sourceC1659) = raw24275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24275; decide +kernel
    rw [ha]
    exact (canonical24275 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1659 + difference 2 3) (sourceB1659 + difference 3 2) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1659 + difference 2 3) (sourceB1659 + difference 3 2) sourceC1659) = raw7562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw7562; decide +kernel
    rw [ha]
    exact (canonical7562 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1659 + difference 2 4) (sourceB1659 + difference 4 2) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA1659 + difference 2 4) (sourceB1659 + difference 4 2) sourceC1659) = raw24276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24276; decide +kernel
    rw [ha]
    exact (canonical24276 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1659 + difference 2 5) (sourceB1659 + difference 5 2) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1659 + difference 2 5) (sourceB1659 + difference 5 2) sourceC1659) = raw24277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24277; decide +kernel
    rw [ha]
    exact (canonical24277 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1659 + difference 3 0) (sourceB1659 + difference 0 3) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4167) := by
    have ha : (tripleCharges (sourceA1659 + difference 3 0) (sourceB1659 + difference 0 3) sourceC1659) = raw24278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24278; decide +kernel
    rw [ha]
    exact (canonical24278 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1659 + difference 3 1) (sourceB1659 + difference 1 3) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4539) := by
    have ha : (tripleCharges (sourceA1659 + difference 3 1) (sourceB1659 + difference 1 3) sourceC1659) = raw24279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24279; decide +kernel
    rw [ha]
    exact (canonical24279 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1659 + difference 3 2) (sourceB1659 + difference 2 3) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4539) := by
    have ha : (tripleCharges (sourceA1659 + difference 3 2) (sourceB1659 + difference 2 3) sourceC1659) = raw24280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24280; decide +kernel
    rw [ha]
    exact (canonical24280 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1659 + difference 3 4) (sourceB1659 + difference 4 3) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4575) := by
    have ha : (tripleCharges (sourceA1659 + difference 3 4) (sourceB1659 + difference 4 3) sourceC1659) = raw24281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24281; decide +kernel
    rw [ha]
    exact (canonical24281 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1659 + difference 3 5) (sourceB1659 + difference 5 3) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1659 + difference 3 5) (sourceB1659 + difference 5 3) sourceC1659) = raw24282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24282; decide +kernel
    rw [ha]
    exact (canonical24282 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1659 + difference 4 0) (sourceB1659 + difference 0 4) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4185) := by
    have ha : (tripleCharges (sourceA1659 + difference 4 0) (sourceB1659 + difference 0 4) sourceC1659) = raw24283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24283; decide +kernel
    rw [ha]
    exact (canonical24283 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1659 + difference 4 1) (sourceB1659 + difference 1 4) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1659 + difference 4 1) (sourceB1659 + difference 1 4) sourceC1659) = raw24284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24284; decide +kernel
    rw [ha]
    exact (canonical24284 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1659 + difference 4 2) (sourceB1659 + difference 2 4) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1659 + difference 4 2) (sourceB1659 + difference 2 4) sourceC1659) = raw24285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24285; decide +kernel
    rw [ha]
    exact (canonical24285 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1659 + difference 4 3) (sourceB1659 + difference 3 4) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1659 + difference 4 3) (sourceB1659 + difference 3 4) sourceC1659) = raw7570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw7570; decide +kernel
    rw [ha]
    exact (canonical7570 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1659 + difference 4 5) (sourceB1659 + difference 5 4) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1659 + difference 4 5) (sourceB1659 + difference 5 4) sourceC1659) = raw24286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw24286; decide +kernel
    rw [ha]
    exact (canonical24286 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1659 + difference 5 0) (sourceB1659 + difference 0 5) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4166) := by
    have ha : (tripleCharges (sourceA1659 + difference 5 0) (sourceB1659 + difference 0 5) sourceC1659) = raw20540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw20540; decide +kernel
    rw [ha]
    exact (canonical20540 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1659 + difference 5 1) (sourceB1659 + difference 1 5) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA1659 + difference 5 1) (sourceB1659 + difference 1 5) sourceC1659) = raw20541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw20541; decide +kernel
    rw [ha]
    exact (canonical20541 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1659 + difference 5 2) (sourceB1659 + difference 2 5) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA1659 + difference 5 2) (sourceB1659 + difference 2 5) sourceC1659) = raw20542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw20542; decide +kernel
    rw [ha]
    exact (canonical20542 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1659 + difference 5 3) (sourceB1659 + difference 3 5) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA1659 + difference 5 3) (sourceB1659 + difference 3 5) sourceC1659) = raw4392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw4392; decide +kernel
    rw [ha]
    exact (canonical4392 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1659 + difference 5 4) (sourceB1659 + difference 4 5) sourceC1659) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA1659 + difference 5 4) (sourceB1659 + difference 4 5) sourceC1659) = raw4388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1659 sourceB1659 sourceC1659 difference raw4388; decide +kernel
    rw [ha]
    exact (canonical4388 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1659 sourceB1659 sourceC1659
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1659, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1660 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1660 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1660 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm1660 : Integer.Sparse Master := [(Sum.inr 593, 2), (Sum.inr 594, 1), (Sum.inr 595, 1), (Sum.inr 613, 1), (Sum.inr 1122, 2), (Sum.inr 1123, 2), (Sum.inr 1124, 2), (Sum.inr 1138, 2), (Sum.inr 1188, 2), (Sum.inr 1190, 1), (Sum.inr 1193, 1), (Sum.inr 1293, 2), (Sum.inr 1294, 3), (Sum.inr 1297, 1), (Sum.inr 1305, 1), (Sum.inr 1311, 1), (Sum.inr 2954, 2), (Sum.inr 3054, 1), (Sum.inr 3120, 1), (Sum.inr 3121, 1)]

theorem sourceEq1660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1660 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1660 + difference 0 1) (sourceB1660 + difference 1 0) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA1660 + difference 0 1) (sourceB1660 + difference 1 0) sourceC1660) = raw7588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw7588; decide +kernel
    rw [ha]
    exact (canonical7588 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1660 + difference 0 2) (sourceB1660 + difference 2 0) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA1660 + difference 0 2) (sourceB1660 + difference 2 0) sourceC1660) = raw7589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw7589; decide +kernel
    rw [ha]
    exact (canonical7589 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1660 + difference 0 3) (sourceB1660 + difference 3 0) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA1660 + difference 0 3) (sourceB1660 + difference 3 0) sourceC1660) = raw4425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw4425; decide +kernel
    rw [ha]
    exact (canonical4425 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1660 + difference 0 4) (sourceB1660 + difference 4 0) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA1660 + difference 0 4) (sourceB1660 + difference 4 0) sourceC1660) = raw4420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw4420; decide +kernel
    rw [ha]
    exact (canonical4420 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1660 + difference 0 5) (sourceB1660 + difference 5 0) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA1660 + difference 0 5) (sourceB1660 + difference 5 0) sourceC1660) = raw7590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw7590; decide +kernel
    rw [ha]
    exact (canonical7590 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1660 + difference 1 0) (sourceB1660 + difference 0 1) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 593) := by
    have ha : (tripleCharges (sourceA1660 + difference 1 0) (sourceB1660 + difference 0 1) sourceC1660) = raw24287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24287; decide +kernel
    rw [ha]
    exact (canonical24287 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1660 + difference 1 2) (sourceB1660 + difference 2 1) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1122) := by
    have ha : (tripleCharges (sourceA1660 + difference 1 2) (sourceB1660 + difference 2 1) sourceC1660) = raw24288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24288; decide +kernel
    rw [ha]
    exact (canonical24288 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1660 + difference 1 3) (sourceB1660 + difference 3 1) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1660 + difference 1 3) (sourceB1660 + difference 3 1) sourceC1660) = raw7579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw7579; decide +kernel
    rw [ha]
    exact (canonical7579 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1660 + difference 1 4) (sourceB1660 + difference 4 1) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1660 + difference 1 4) (sourceB1660 + difference 4 1) sourceC1660) = raw24289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24289; decide +kernel
    rw [ha]
    exact (canonical24289 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1660 + difference 1 5) (sourceB1660 + difference 5 1) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1660 + difference 1 5) (sourceB1660 + difference 5 1) sourceC1660) = raw24290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24290; decide +kernel
    rw [ha]
    exact (canonical24290 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1660 + difference 2 0) (sourceB1660 + difference 0 2) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 593) := by
    have ha : (tripleCharges (sourceA1660 + difference 2 0) (sourceB1660 + difference 0 2) sourceC1660) = raw24291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24291; decide +kernel
    rw [ha]
    exact (canonical24291 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1660 + difference 2 1) (sourceB1660 + difference 1 2) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1122) := by
    have ha : (tripleCharges (sourceA1660 + difference 2 1) (sourceB1660 + difference 1 2) sourceC1660) = raw24292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24292; decide +kernel
    rw [ha]
    exact (canonical24292 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1660 + difference 2 3) (sourceB1660 + difference 3 2) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1660 + difference 2 3) (sourceB1660 + difference 3 2) sourceC1660) = raw7583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw7583; decide +kernel
    rw [ha]
    exact (canonical7583 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1660 + difference 2 4) (sourceB1660 + difference 4 2) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1660 + difference 2 4) (sourceB1660 + difference 4 2) sourceC1660) = raw24293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24293; decide +kernel
    rw [ha]
    exact (canonical24293 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1660 + difference 2 5) (sourceB1660 + difference 5 2) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1660 + difference 2 5) (sourceB1660 + difference 5 2) sourceC1660) = raw24294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24294; decide +kernel
    rw [ha]
    exact (canonical24294 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1660 + difference 3 0) (sourceB1660 + difference 0 3) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 595) := by
    have ha : (tripleCharges (sourceA1660 + difference 3 0) (sourceB1660 + difference 0 3) sourceC1660) = raw24295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24295; decide +kernel
    rw [ha]
    exact (canonical24295 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1660 + difference 3 1) (sourceB1660 + difference 1 3) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1124) := by
    have ha : (tripleCharges (sourceA1660 + difference 3 1) (sourceB1660 + difference 1 3) sourceC1660) = raw24296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24296; decide +kernel
    rw [ha]
    exact (canonical24296 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1660 + difference 3 2) (sourceB1660 + difference 2 3) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1124) := by
    have ha : (tripleCharges (sourceA1660 + difference 3 2) (sourceB1660 + difference 2 3) sourceC1660) = raw24297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24297; decide +kernel
    rw [ha]
    exact (canonical24297 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1660 + difference 3 4) (sourceB1660 + difference 4 3) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1193) := by
    have ha : (tripleCharges (sourceA1660 + difference 3 4) (sourceB1660 + difference 4 3) sourceC1660) = raw24298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24298; decide +kernel
    rw [ha]
    exact (canonical24298 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1660 + difference 3 5) (sourceB1660 + difference 5 3) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1660 + difference 3 5) (sourceB1660 + difference 5 3) sourceC1660) = raw24299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24299; decide +kernel
    rw [ha]
    exact (canonical24299 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1660 + difference 4 0) (sourceB1660 + difference 0 4) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 613) := by
    have ha : (tripleCharges (sourceA1660 + difference 4 0) (sourceB1660 + difference 0 4) sourceC1660) = raw24300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24300; decide +kernel
    rw [ha]
    exact (canonical24300 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1660 + difference 4 1) (sourceB1660 + difference 1 4) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1660 + difference 4 1) (sourceB1660 + difference 1 4) sourceC1660) = raw24301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24301; decide +kernel
    rw [ha]
    exact (canonical24301 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1660 + difference 4 2) (sourceB1660 + difference 2 4) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1660 + difference 4 2) (sourceB1660 + difference 2 4) sourceC1660) = raw24302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24302; decide +kernel
    rw [ha]
    exact (canonical24302 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1660 + difference 4 3) (sourceB1660 + difference 3 4) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1660 + difference 4 3) (sourceB1660 + difference 3 4) sourceC1660) = raw7591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw7591; decide +kernel
    rw [ha]
    exact (canonical7591 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1660 + difference 4 5) (sourceB1660 + difference 5 4) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1660 + difference 4 5) (sourceB1660 + difference 5 4) sourceC1660) = raw24303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw24303; decide +kernel
    rw [ha]
    exact (canonical24303 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1660 + difference 5 0) (sourceB1660 + difference 0 5) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 594) := by
    have ha : (tripleCharges (sourceA1660 + difference 5 0) (sourceB1660 + difference 0 5) sourceC1660) = raw20557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw20557; decide +kernel
    rw [ha]
    exact (canonical20557 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1660 + difference 5 1) (sourceB1660 + difference 1 5) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1660 + difference 5 1) (sourceB1660 + difference 1 5) sourceC1660) = raw20558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw20558; decide +kernel
    rw [ha]
    exact (canonical20558 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1660 + difference 5 2) (sourceB1660 + difference 2 5) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1660 + difference 5 2) (sourceB1660 + difference 2 5) sourceC1660) = raw20559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw20559; decide +kernel
    rw [ha]
    exact (canonical20559 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1660 + difference 5 3) (sourceB1660 + difference 3 5) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA1660 + difference 5 3) (sourceB1660 + difference 3 5) sourceC1660) = raw4421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw4421; decide +kernel
    rw [ha]
    exact (canonical4421 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1660 + difference 5 4) (sourceB1660 + difference 4 5) sourceC1660) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1660 + difference 5 4) (sourceB1660 + difference 4 5) sourceC1660) = raw4416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1660 sourceB1660 sourceC1660 difference raw4416; decide +kernel
    rw [ha]
    exact (canonical4416 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1660 sourceB1660 sourceC1660
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1660, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1661 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1661 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1661 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceForm1661 : Integer.Sparse Master := [(Sum.inr 4176, 2), (Sum.inr 4178, 1), (Sum.inr 4179, 1), (Sum.inr 4188, 1), (Sum.inr 4545, 2), (Sum.inr 4547, 2), (Sum.inr 4548, 2), (Sum.inr 4556, 2), (Sum.inr 4602, 2), (Sum.inr 4607, 2), (Sum.inr 4608, 1), (Sum.inr 4609, 1), (Sum.inr 4611, 1), (Sum.inr 4612, 1), (Sum.inr 4616, 2), (Sum.inr 4617, 1), (Sum.inr 4620, 1), (Sum.inr 5163, 2), (Sum.inr 5274, 1), (Sum.inr 5291, 1), (Sum.inr 5304, 1)]

theorem sourceEq1661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1661 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1661 + difference 0 1) (sourceB1661 + difference 1 0) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA1661 + difference 0 1) (sourceB1661 + difference 1 0) sourceC1661) = raw24304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24304; decide +kernel
    rw [ha]
    exact (canonical24304 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1661 + difference 0 2) (sourceB1661 + difference 2 0) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA1661 + difference 0 2) (sourceB1661 + difference 2 0) sourceC1661) = raw24305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24305; decide +kernel
    rw [ha]
    exact (canonical24305 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1661 + difference 0 3) (sourceB1661 + difference 3 0) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA1661 + difference 0 3) (sourceB1661 + difference 3 0) sourceC1661) = raw24306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24306; decide +kernel
    rw [ha]
    exact (canonical24306 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1661 + difference 0 4) (sourceB1661 + difference 4 0) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA1661 + difference 0 4) (sourceB1661 + difference 4 0) sourceC1661) = raw24307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24307; decide +kernel
    rw [ha]
    exact (canonical24307 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1661 + difference 0 5) (sourceB1661 + difference 5 0) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA1661 + difference 0 5) (sourceB1661 + difference 5 0) sourceC1661) = raw24308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24308; decide +kernel
    rw [ha]
    exact (canonical24308 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1661 + difference 1 0) (sourceB1661 + difference 0 1) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4176) := by
    have ha : (tripleCharges (sourceA1661 + difference 1 0) (sourceB1661 + difference 0 1) sourceC1661) = raw24309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24309; decide +kernel
    rw [ha]
    exact (canonical24309 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1661 + difference 1 2) (sourceB1661 + difference 2 1) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4545) := by
    have ha : (tripleCharges (sourceA1661 + difference 1 2) (sourceB1661 + difference 2 1) sourceC1661) = raw24310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24310; decide +kernel
    rw [ha]
    exact (canonical24310 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1661 + difference 1 3) (sourceB1661 + difference 3 1) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1661 + difference 1 3) (sourceB1661 + difference 3 1) sourceC1661) = raw24311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24311; decide +kernel
    rw [ha]
    exact (canonical24311 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1661 + difference 1 4) (sourceB1661 + difference 4 1) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1661 + difference 1 4) (sourceB1661 + difference 4 1) sourceC1661) = raw24312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24312; decide +kernel
    rw [ha]
    exact (canonical24312 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1661 + difference 1 5) (sourceB1661 + difference 5 1) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1661 + difference 1 5) (sourceB1661 + difference 5 1) sourceC1661) = raw24313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24313; decide +kernel
    rw [ha]
    exact (canonical24313 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1661 + difference 2 0) (sourceB1661 + difference 0 2) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4176) := by
    have ha : (tripleCharges (sourceA1661 + difference 2 0) (sourceB1661 + difference 0 2) sourceC1661) = raw24314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24314; decide +kernel
    rw [ha]
    exact (canonical24314 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1661 + difference 2 1) (sourceB1661 + difference 1 2) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4545) := by
    have ha : (tripleCharges (sourceA1661 + difference 2 1) (sourceB1661 + difference 1 2) sourceC1661) = raw24315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24315; decide +kernel
    rw [ha]
    exact (canonical24315 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1661 + difference 2 3) (sourceB1661 + difference 3 2) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1661 + difference 2 3) (sourceB1661 + difference 3 2) sourceC1661) = raw24316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24316; decide +kernel
    rw [ha]
    exact (canonical24316 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1661 + difference 2 4) (sourceB1661 + difference 4 2) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1661 + difference 2 4) (sourceB1661 + difference 4 2) sourceC1661) = raw24317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24317; decide +kernel
    rw [ha]
    exact (canonical24317 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1661 + difference 2 5) (sourceB1661 + difference 5 2) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1661 + difference 2 5) (sourceB1661 + difference 5 2) sourceC1661) = raw24318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24318; decide +kernel
    rw [ha]
    exact (canonical24318 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1661 + difference 3 0) (sourceB1661 + difference 0 3) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4188) := by
    have ha : (tripleCharges (sourceA1661 + difference 3 0) (sourceB1661 + difference 0 3) sourceC1661) = raw24319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24319; decide +kernel
    rw [ha]
    exact (canonical24319 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1661 + difference 3 1) (sourceB1661 + difference 1 3) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4556) := by
    have ha : (tripleCharges (sourceA1661 + difference 3 1) (sourceB1661 + difference 1 3) sourceC1661) = raw24320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24320; decide +kernel
    rw [ha]
    exact (canonical24320 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1661 + difference 3 2) (sourceB1661 + difference 2 3) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4556) := by
    have ha : (tripleCharges (sourceA1661 + difference 3 2) (sourceB1661 + difference 2 3) sourceC1661) = raw24321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24321; decide +kernel
    rw [ha]
    exact (canonical24321 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1661 + difference 3 4) (sourceB1661 + difference 4 3) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1661 + difference 3 4) (sourceB1661 + difference 4 3) sourceC1661) = raw24322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24322; decide +kernel
    rw [ha]
    exact (canonical24322 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1661 + difference 3 5) (sourceB1661 + difference 5 3) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4620) := by
    have ha : (tripleCharges (sourceA1661 + difference 3 5) (sourceB1661 + difference 5 3) sourceC1661) = raw24323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24323; decide +kernel
    rw [ha]
    exact (canonical24323 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1661 + difference 4 0) (sourceB1661 + difference 0 4) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4179) := by
    have ha : (tripleCharges (sourceA1661 + difference 4 0) (sourceB1661 + difference 0 4) sourceC1661) = raw24324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24324; decide +kernel
    rw [ha]
    exact (canonical24324 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1661 + difference 4 1) (sourceB1661 + difference 1 4) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4548) := by
    have ha : (tripleCharges (sourceA1661 + difference 4 1) (sourceB1661 + difference 1 4) sourceC1661) = raw24325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24325; decide +kernel
    rw [ha]
    exact (canonical24325 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1661 + difference 4 2) (sourceB1661 + difference 2 4) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4548) := by
    have ha : (tripleCharges (sourceA1661 + difference 4 2) (sourceB1661 + difference 2 4) sourceC1661) = raw24326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24326; decide +kernel
    rw [ha]
    exact (canonical24326 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1661 + difference 4 3) (sourceB1661 + difference 3 4) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1661 + difference 4 3) (sourceB1661 + difference 3 4) sourceC1661) = raw24327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24327; decide +kernel
    rw [ha]
    exact (canonical24327 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1661 + difference 4 5) (sourceB1661 + difference 5 4) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1661 + difference 4 5) (sourceB1661 + difference 5 4) sourceC1661) = raw24328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24328; decide +kernel
    rw [ha]
    exact (canonical24328 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1661 + difference 5 0) (sourceB1661 + difference 0 5) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4178) := by
    have ha : (tripleCharges (sourceA1661 + difference 5 0) (sourceB1661 + difference 0 5) sourceC1661) = raw24329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24329; decide +kernel
    rw [ha]
    exact (canonical24329 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1661 + difference 5 1) (sourceB1661 + difference 1 5) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1661 + difference 5 1) (sourceB1661 + difference 1 5) sourceC1661) = raw24330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24330; decide +kernel
    rw [ha]
    exact (canonical24330 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1661 + difference 5 2) (sourceB1661 + difference 2 5) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1661 + difference 5 2) (sourceB1661 + difference 2 5) sourceC1661) = raw24331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24331; decide +kernel
    rw [ha]
    exact (canonical24331 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1661 + difference 5 3) (sourceB1661 + difference 3 5) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1661 + difference 5 3) (sourceB1661 + difference 3 5) sourceC1661) = raw24332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24332; decide +kernel
    rw [ha]
    exact (canonical24332 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1661 + difference 5 4) (sourceB1661 + difference 4 5) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1661 + difference 5 4) (sourceB1661 + difference 4 5) sourceC1661) = raw24333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24333; decide +kernel
    rw [ha]
    exact (canonical24333 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1661 sourceB1661 sourceC1661
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1661, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1662 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1662 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1662 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceForm1662 : Integer.Sparse Master := [(Sum.inr 604, 2), (Sum.inr 606, 1), (Sum.inr 607, 1), (Sum.inr 616, 1), (Sum.inr 1130, 2), (Sum.inr 1132, 2), (Sum.inr 1133, 2), (Sum.inr 1141, 2), (Sum.inr 1241, 2), (Sum.inr 1243, 1), (Sum.inr 1245, 1), (Sum.inr 1267, 2), (Sum.inr 1269, 1), (Sum.inr 1274, 1), (Sum.inr 1291, 2), (Sum.inr 1292, 1), (Sum.inr 1295, 1), (Sum.inr 2961, 2), (Sum.inr 3103, 1), (Sum.inr 3112, 1), (Sum.inr 3119, 1)]

theorem sourceEq1662 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1662 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1662 + difference 0 1) (sourceB1662 + difference 1 0) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2961) := by
    have ha : (tripleCharges (sourceA1662 + difference 0 1) (sourceB1662 + difference 1 0) sourceC1662) = raw24334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24334; decide +kernel
    rw [ha]
    exact (canonical24334 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1662 + difference 0 2) (sourceB1662 + difference 2 0) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2961) := by
    have ha : (tripleCharges (sourceA1662 + difference 0 2) (sourceB1662 + difference 2 0) sourceC1662) = raw24335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24335; decide +kernel
    rw [ha]
    exact (canonical24335 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1662 + difference 0 3) (sourceB1662 + difference 3 0) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA1662 + difference 0 3) (sourceB1662 + difference 3 0) sourceC1662) = raw24336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24336; decide +kernel
    rw [ha]
    exact (canonical24336 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1662 + difference 0 4) (sourceB1662 + difference 4 0) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA1662 + difference 0 4) (sourceB1662 + difference 4 0) sourceC1662) = raw24337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24337; decide +kernel
    rw [ha]
    exact (canonical24337 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1662 + difference 0 5) (sourceB1662 + difference 5 0) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA1662 + difference 0 5) (sourceB1662 + difference 5 0) sourceC1662) = raw24338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24338; decide +kernel
    rw [ha]
    exact (canonical24338 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1662 + difference 1 0) (sourceB1662 + difference 0 1) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 604) := by
    have ha : (tripleCharges (sourceA1662 + difference 1 0) (sourceB1662 + difference 0 1) sourceC1662) = raw24339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24339; decide +kernel
    rw [ha]
    exact (canonical24339 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1662 + difference 1 2) (sourceB1662 + difference 2 1) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1130) := by
    have ha : (tripleCharges (sourceA1662 + difference 1 2) (sourceB1662 + difference 2 1) sourceC1662) = raw24340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24340; decide +kernel
    rw [ha]
    exact (canonical24340 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1662 + difference 1 3) (sourceB1662 + difference 3 1) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1662 + difference 1 3) (sourceB1662 + difference 3 1) sourceC1662) = raw24341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24341; decide +kernel
    rw [ha]
    exact (canonical24341 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1662 + difference 1 4) (sourceB1662 + difference 4 1) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1662 + difference 1 4) (sourceB1662 + difference 4 1) sourceC1662) = raw24342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24342; decide +kernel
    rw [ha]
    exact (canonical24342 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1662 + difference 1 5) (sourceB1662 + difference 5 1) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1662 + difference 1 5) (sourceB1662 + difference 5 1) sourceC1662) = raw24343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24343; decide +kernel
    rw [ha]
    exact (canonical24343 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1662 + difference 2 0) (sourceB1662 + difference 0 2) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 604) := by
    have ha : (tripleCharges (sourceA1662 + difference 2 0) (sourceB1662 + difference 0 2) sourceC1662) = raw24344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24344; decide +kernel
    rw [ha]
    exact (canonical24344 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1662 + difference 2 1) (sourceB1662 + difference 1 2) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1130) := by
    have ha : (tripleCharges (sourceA1662 + difference 2 1) (sourceB1662 + difference 1 2) sourceC1662) = raw24345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24345; decide +kernel
    rw [ha]
    exact (canonical24345 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1662 + difference 2 3) (sourceB1662 + difference 3 2) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1662 + difference 2 3) (sourceB1662 + difference 3 2) sourceC1662) = raw24346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24346; decide +kernel
    rw [ha]
    exact (canonical24346 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1662 + difference 2 4) (sourceB1662 + difference 4 2) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1662 + difference 2 4) (sourceB1662 + difference 4 2) sourceC1662) = raw24347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24347; decide +kernel
    rw [ha]
    exact (canonical24347 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1662 + difference 2 5) (sourceB1662 + difference 5 2) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1662 + difference 2 5) (sourceB1662 + difference 5 2) sourceC1662) = raw24348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24348; decide +kernel
    rw [ha]
    exact (canonical24348 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1662 + difference 3 0) (sourceB1662 + difference 0 3) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 616) := by
    have ha : (tripleCharges (sourceA1662 + difference 3 0) (sourceB1662 + difference 0 3) sourceC1662) = raw24349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24349; decide +kernel
    rw [ha]
    exact (canonical24349 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1662 + difference 3 1) (sourceB1662 + difference 1 3) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1141) := by
    have ha : (tripleCharges (sourceA1662 + difference 3 1) (sourceB1662 + difference 1 3) sourceC1662) = raw24350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24350; decide +kernel
    rw [ha]
    exact (canonical24350 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1662 + difference 3 2) (sourceB1662 + difference 2 3) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1141) := by
    have ha : (tripleCharges (sourceA1662 + difference 3 2) (sourceB1662 + difference 2 3) sourceC1662) = raw24351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24351; decide +kernel
    rw [ha]
    exact (canonical24351 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1662 + difference 3 4) (sourceB1662 + difference 4 3) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1662 + difference 3 4) (sourceB1662 + difference 4 3) sourceC1662) = raw24352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24352; decide +kernel
    rw [ha]
    exact (canonical24352 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1662 + difference 3 5) (sourceB1662 + difference 5 3) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1295) := by
    have ha : (tripleCharges (sourceA1662 + difference 3 5) (sourceB1662 + difference 5 3) sourceC1662) = raw24353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24353; decide +kernel
    rw [ha]
    exact (canonical24353 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1662 + difference 4 0) (sourceB1662 + difference 0 4) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1662 + difference 4 0) (sourceB1662 + difference 0 4) sourceC1662) = raw24354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24354; decide +kernel
    rw [ha]
    exact (canonical24354 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1662 + difference 4 1) (sourceB1662 + difference 1 4) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1133) := by
    have ha : (tripleCharges (sourceA1662 + difference 4 1) (sourceB1662 + difference 1 4) sourceC1662) = raw24355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24355; decide +kernel
    rw [ha]
    exact (canonical24355 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1662 + difference 4 2) (sourceB1662 + difference 2 4) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1133) := by
    have ha : (tripleCharges (sourceA1662 + difference 4 2) (sourceB1662 + difference 2 4) sourceC1662) = raw24356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24356; decide +kernel
    rw [ha]
    exact (canonical24356 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1662 + difference 4 3) (sourceB1662 + difference 3 4) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1662 + difference 4 3) (sourceB1662 + difference 3 4) sourceC1662) = raw24357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24357; decide +kernel
    rw [ha]
    exact (canonical24357 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1662 + difference 4 5) (sourceB1662 + difference 5 4) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1292) := by
    have ha : (tripleCharges (sourceA1662 + difference 4 5) (sourceB1662 + difference 5 4) sourceC1662) = raw24358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24358; decide +kernel
    rw [ha]
    exact (canonical24358 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1662 + difference 5 0) (sourceB1662 + difference 0 5) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 606) := by
    have ha : (tripleCharges (sourceA1662 + difference 5 0) (sourceB1662 + difference 0 5) sourceC1662) = raw24359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24359; decide +kernel
    rw [ha]
    exact (canonical24359 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1662 + difference 5 1) (sourceB1662 + difference 1 5) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1662 + difference 5 1) (sourceB1662 + difference 1 5) sourceC1662) = raw24360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24360; decide +kernel
    rw [ha]
    exact (canonical24360 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1662 + difference 5 2) (sourceB1662 + difference 2 5) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1662 + difference 5 2) (sourceB1662 + difference 2 5) sourceC1662) = raw24361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24361; decide +kernel
    rw [ha]
    exact (canonical24361 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1662 + difference 5 3) (sourceB1662 + difference 3 5) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1662 + difference 5 3) (sourceB1662 + difference 3 5) sourceC1662) = raw24362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24362; decide +kernel
    rw [ha]
    exact (canonical24362 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1662 + difference 5 4) (sourceB1662 + difference 4 5) sourceC1662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1269) := by
    have ha : (tripleCharges (sourceA1662 + difference 5 4) (sourceB1662 + difference 4 5) sourceC1662) = raw24363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1662 sourceB1662 sourceC1662 difference raw24363; decide +kernel
    rw [ha]
    exact (canonical24363 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1662 sourceB1662 sourceC1662
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1662, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1663 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1663 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1663 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceForm1663 : Integer.Sparse Master := [(Sum.inr 1512, 2), (Sum.inr 1513, 1), (Sum.inr 1520, 1), (Sum.inr 1526, 1), (Sum.inr 2657, 2), (Sum.inr 2683, 1), (Sum.inr 2737, 1), (Sum.inr 3259, 2), (Sum.inr 3266, 2), (Sum.inr 3271, 2), (Sum.inr 3293, 2), (Sum.inr 3296, 2), (Sum.inr 3300, 1), (Sum.inr 3301, 1), (Sum.inr 3302, 1), (Sum.inr 3303, 2), (Sum.inr 3306, 1), (Sum.inr 3547, 1), (Sum.inr 3564, 2), (Sum.inr 3582, 1), (Sum.inr 3583, 1)]

theorem sourceEq1663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1663 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1663 + difference 0 1) (sourceB1663 + difference 1 0) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA1663 + difference 0 1) (sourceB1663 + difference 1 0) sourceC1663) = raw24364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24364; decide +kernel
    rw [ha]
    exact (canonical24364 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1663 + difference 0 2) (sourceB1663 + difference 2 0) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA1663 + difference 0 2) (sourceB1663 + difference 2 0) sourceC1663) = raw24365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24365; decide +kernel
    rw [ha]
    exact (canonical24365 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1663 + difference 0 3) (sourceB1663 + difference 3 0) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA1663 + difference 0 3) (sourceB1663 + difference 3 0) sourceC1663) = raw24366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24366; decide +kernel
    rw [ha]
    exact (canonical24366 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1663 + difference 0 4) (sourceB1663 + difference 4 0) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA1663 + difference 0 4) (sourceB1663 + difference 4 0) sourceC1663) = raw24367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24367; decide +kernel
    rw [ha]
    exact (canonical24367 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1663 + difference 0 5) (sourceB1663 + difference 5 0) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA1663 + difference 0 5) (sourceB1663 + difference 5 0) sourceC1663) = raw24368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24368; decide +kernel
    rw [ha]
    exact (canonical24368 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1663 + difference 1 0) (sourceB1663 + difference 0 1) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1663 + difference 1 0) (sourceB1663 + difference 0 1) sourceC1663) = raw24369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24369; decide +kernel
    rw [ha]
    exact (canonical24369 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1663 + difference 1 2) (sourceB1663 + difference 2 1) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3259) := by
    have ha : (tripleCharges (sourceA1663 + difference 1 2) (sourceB1663 + difference 2 1) sourceC1663) = raw24370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24370; decide +kernel
    rw [ha]
    exact (canonical24370 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1663 + difference 1 3) (sourceB1663 + difference 3 1) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1663 + difference 1 3) (sourceB1663 + difference 3 1) sourceC1663) = raw24371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24371; decide +kernel
    rw [ha]
    exact (canonical24371 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1663 + difference 1 4) (sourceB1663 + difference 4 1) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1663 + difference 1 4) (sourceB1663 + difference 4 1) sourceC1663) = raw24372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24372; decide +kernel
    rw [ha]
    exact (canonical24372 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1663 + difference 1 5) (sourceB1663 + difference 5 1) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1663 + difference 1 5) (sourceB1663 + difference 5 1) sourceC1663) = raw24373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24373; decide +kernel
    rw [ha]
    exact (canonical24373 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1663 + difference 2 0) (sourceB1663 + difference 0 2) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1663 + difference 2 0) (sourceB1663 + difference 0 2) sourceC1663) = raw24374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24374; decide +kernel
    rw [ha]
    exact (canonical24374 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1663 + difference 2 1) (sourceB1663 + difference 1 2) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3259) := by
    have ha : (tripleCharges (sourceA1663 + difference 2 1) (sourceB1663 + difference 1 2) sourceC1663) = raw24375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24375; decide +kernel
    rw [ha]
    exact (canonical24375 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1663 + difference 2 3) (sourceB1663 + difference 3 2) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1663 + difference 2 3) (sourceB1663 + difference 3 2) sourceC1663) = raw24376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24376; decide +kernel
    rw [ha]
    exact (canonical24376 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1663 + difference 2 4) (sourceB1663 + difference 4 2) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1663 + difference 2 4) (sourceB1663 + difference 4 2) sourceC1663) = raw24377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24377; decide +kernel
    rw [ha]
    exact (canonical24377 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1663 + difference 2 5) (sourceB1663 + difference 5 2) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1663 + difference 2 5) (sourceB1663 + difference 5 2) sourceC1663) = raw24378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24378; decide +kernel
    rw [ha]
    exact (canonical24378 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1663 + difference 3 0) (sourceB1663 + difference 0 3) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1526) := by
    have ha : (tripleCharges (sourceA1663 + difference 3 0) (sourceB1663 + difference 0 3) sourceC1663) = raw24379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24379; decide +kernel
    rw [ha]
    exact (canonical24379 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1663 + difference 3 1) (sourceB1663 + difference 1 3) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA1663 + difference 3 1) (sourceB1663 + difference 1 3) sourceC1663) = raw24380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24380; decide +kernel
    rw [ha]
    exact (canonical24380 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1663 + difference 3 2) (sourceB1663 + difference 2 3) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA1663 + difference 3 2) (sourceB1663 + difference 2 3) sourceC1663) = raw24381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24381; decide +kernel
    rw [ha]
    exact (canonical24381 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1663 + difference 3 4) (sourceB1663 + difference 4 3) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1663 + difference 3 4) (sourceB1663 + difference 4 3) sourceC1663) = raw24382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24382; decide +kernel
    rw [ha]
    exact (canonical24382 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1663 + difference 3 5) (sourceB1663 + difference 5 3) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA1663 + difference 3 5) (sourceB1663 + difference 5 3) sourceC1663) = raw24383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24383; decide +kernel
    rw [ha]
    exact (canonical24383 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1663 + difference 4 0) (sourceB1663 + difference 0 4) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1663 + difference 4 0) (sourceB1663 + difference 0 4) sourceC1663) = raw24384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24384; decide +kernel
    rw [ha]
    exact (canonical24384 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1663 + difference 4 1) (sourceB1663 + difference 1 4) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA1663 + difference 4 1) (sourceB1663 + difference 1 4) sourceC1663) = raw24385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24385; decide +kernel
    rw [ha]
    exact (canonical24385 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1663 + difference 4 2) (sourceB1663 + difference 2 4) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA1663 + difference 4 2) (sourceB1663 + difference 2 4) sourceC1663) = raw24386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24386; decide +kernel
    rw [ha]
    exact (canonical24386 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1663 + difference 4 3) (sourceB1663 + difference 3 4) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1663 + difference 4 3) (sourceB1663 + difference 3 4) sourceC1663) = raw24387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24387; decide +kernel
    rw [ha]
    exact (canonical24387 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1663 + difference 4 5) (sourceB1663 + difference 5 4) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1663 + difference 4 5) (sourceB1663 + difference 5 4) sourceC1663) = raw24388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24388; decide +kernel
    rw [ha]
    exact (canonical24388 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1663 + difference 5 0) (sourceB1663 + difference 0 5) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1663 + difference 5 0) (sourceB1663 + difference 0 5) sourceC1663) = raw24389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24389; decide +kernel
    rw [ha]
    exact (canonical24389 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1663 + difference 5 1) (sourceB1663 + difference 1 5) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1663 + difference 5 1) (sourceB1663 + difference 1 5) sourceC1663) = raw24390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24390; decide +kernel
    rw [ha]
    exact (canonical24390 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1663 + difference 5 2) (sourceB1663 + difference 2 5) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1663 + difference 5 2) (sourceB1663 + difference 2 5) sourceC1663) = raw24391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24391; decide +kernel
    rw [ha]
    exact (canonical24391 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1663 + difference 5 3) (sourceB1663 + difference 3 5) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1663 + difference 5 3) (sourceB1663 + difference 3 5) sourceC1663) = raw24392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24392; decide +kernel
    rw [ha]
    exact (canonical24392 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1663 + difference 5 4) (sourceB1663 + difference 4 5) sourceC1663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1663 + difference 5 4) (sourceB1663 + difference 4 5) sourceC1663) = raw24393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1663 sourceB1663 sourceC1663 difference raw24393; decide +kernel
    rw [ha]
    exact (canonical24393 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1663 sourceB1663 sourceC1663
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1663, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
