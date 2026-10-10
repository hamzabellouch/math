import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical293
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical294
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical295

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2720 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2720 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC2720 : Charge := ![-4, -1, 0, 1, 1, 3]
def sourceForm2720 : Integer.Sparse Master := [(Sum.inr 1690, 1), (Sum.inr 2184, 1), (Sum.inr 3255, 1), (Sum.inr 3264, 2), (Sum.inr 3273, 1), (Sum.inr 4064, -1)]

theorem sourceEq2720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2720 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2720 + difference 0 2) (sourceB2720 + difference 2 0) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1690) := by
    have ha : (tripleCharges (sourceA2720 + difference 0 2) (sourceB2720 + difference 2 0) sourceC2720) = raw37622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37622; decide +kernel
    rw [ha]
    exact (canonical37622 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2720 + difference 1 2) (sourceB2720 + difference 2 1) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3273) := by
    have ha : (tripleCharges (sourceA2720 + difference 1 2) (sourceB2720 + difference 2 1) sourceC2720) = raw37623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37623; decide +kernel
    rw [ha]
    exact (canonical37623 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2720 + difference 2 2) (sourceB2720 + difference 2 2) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3255) := by
    have ha : (tripleCharges (sourceA2720 + difference 2 2) (sourceB2720 + difference 2 2) sourceC2720) = raw37624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37624; decide +kernel
    rw [ha]
    exact (canonical37624 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2720 + difference 3 2) (sourceB2720 + difference 2 3) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA2720 + difference 3 2) (sourceB2720 + difference 2 3) sourceC2720) = raw37625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37625; decide +kernel
    rw [ha]
    exact (canonical37625 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2720 + difference 4 2) (sourceB2720 + difference 2 4) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA2720 + difference 4 2) (sourceB2720 + difference 2 4) sourceC2720) = raw37626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37626; decide +kernel
    rw [ha]
    exact (canonical37626 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2720 + difference 5 2) (sourceB2720 + difference 2 5) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA2720 + difference 5 2) (sourceB2720 + difference 2 5) sourceC2720) = raw37627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37627; decide +kernel
    rw [ha]
    exact (canonical37627 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2720 + sourceB2720) sourceC2720) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (doubleCharges (sourceA2720 + sourceB2720) sourceC2720) = raw37621 := by
      apply Matrix.ext; unfold doubleCharges sourceA2720 sourceB2720 sourceC2720 raw37621; decide +kernel
    rw [ha]
    exact (canonical37621 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2720 sourceB2720 sourceC2720
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2720, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2721 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB2721 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2721 : Charge := ![-4, -1, 0, 1, 1, 3]
def sourceForm2721 : Integer.Sparse Master := [(Sum.inr 968, 1), (Sum.inr 1550, 1), (Sum.inr 1557, 2), (Sum.inr 1666, 1), (Sum.inr 2184, 1), (Sum.inr 4064, -1)]

theorem sourceEq2721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2721 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2721 + difference 0 0) (sourceB2721 + difference 0 0) sourceC2721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA2721 + difference 0 0) (sourceB2721 + difference 0 0) sourceC2721) = raw37627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2721 sourceB2721 sourceC2721 difference raw37627; decide +kernel
    rw [ha]
    exact (canonical37627 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2721 + difference 1 0) (sourceB2721 + difference 0 1) sourceC2721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA2721 + difference 1 0) (sourceB2721 + difference 0 1) sourceC2721) = raw37628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2721 sourceB2721 sourceC2721 difference raw37628; decide +kernel
    rw [ha]
    exact (canonical37628 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2721 + difference 2 0) (sourceB2721 + difference 0 2) sourceC2721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1550) := by
    have ha : (tripleCharges (sourceA2721 + difference 2 0) (sourceB2721 + difference 0 2) sourceC2721) = raw37629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2721 sourceB2721 sourceC2721 difference raw37629; decide +kernel
    rw [ha]
    exact (canonical37629 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2721 + difference 3 0) (sourceB2721 + difference 0 3) sourceC2721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1557) := by
    have ha : (tripleCharges (sourceA2721 + difference 3 0) (sourceB2721 + difference 0 3) sourceC2721) = raw37630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2721 sourceB2721 sourceC2721 difference raw37630; decide +kernel
    rw [ha]
    exact (canonical37630 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2721 + difference 4 0) (sourceB2721 + difference 0 4) sourceC2721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1557) := by
    have ha : (tripleCharges (sourceA2721 + difference 4 0) (sourceB2721 + difference 0 4) sourceC2721) = raw37631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2721 sourceB2721 sourceC2721 difference raw37631; decide +kernel
    rw [ha]
    exact (canonical37631 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2721 + difference 5 0) (sourceB2721 + difference 0 5) sourceC2721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 968) := by
    have ha : (tripleCharges (sourceA2721 + difference 5 0) (sourceB2721 + difference 0 5) sourceC2721) = raw37632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2721 sourceB2721 sourceC2721 difference raw37632; decide +kernel
    rw [ha]
    exact (canonical37632 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2721 + sourceB2721) sourceC2721) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (doubleCharges (sourceA2721 + sourceB2721) sourceC2721) = raw37621 := by
      apply Matrix.ext; unfold doubleCharges sourceA2721 sourceB2721 sourceC2721 raw37621; decide +kernel
    rw [ha]
    exact (canonical37621 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2721 sourceB2721 sourceC2721
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2721, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2722 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2722 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2722 : Charge := ![-4, -1, 0, 1, 1, 3]
def sourceForm2722 : Integer.Sparse Master := [(Sum.inr 760, 1), (Sum.inr 767, 1), (Sum.inr 769, 2), (Sum.inr 840, 1), (Sum.inr 1690, 1), (Sum.inr 4064, -1)]

theorem sourceEq2722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2722 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2722 + difference 0 0) (sourceB2722 + difference 0 0) sourceC2722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1690) := by
    have ha : (tripleCharges (sourceA2722 + difference 0 0) (sourceB2722 + difference 0 0) sourceC2722) = raw37617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2722 sourceB2722 sourceC2722 difference raw37617; decide +kernel
    rw [ha]
    exact (canonical37617 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2722 + difference 1 0) (sourceB2722 + difference 0 1) sourceC2722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 840) := by
    have ha : (tripleCharges (sourceA2722 + difference 1 0) (sourceB2722 + difference 0 1) sourceC2722) = raw37633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2722 sourceB2722 sourceC2722 difference raw37633; decide +kernel
    rw [ha]
    exact (canonical37633 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2722 + difference 2 0) (sourceB2722 + difference 0 2) sourceC2722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 760) := by
    have ha : (tripleCharges (sourceA2722 + difference 2 0) (sourceB2722 + difference 0 2) sourceC2722) = raw37615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2722 sourceB2722 sourceC2722 difference raw37615; decide +kernel
    rw [ha]
    exact (canonical37615 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2722 + difference 3 0) (sourceB2722 + difference 0 3) sourceC2722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 769) := by
    have ha : (tripleCharges (sourceA2722 + difference 3 0) (sourceB2722 + difference 0 3) sourceC2722) = raw37634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2722 sourceB2722 sourceC2722 difference raw37634; decide +kernel
    rw [ha]
    exact (canonical37634 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2722 + difference 4 0) (sourceB2722 + difference 0 4) sourceC2722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 769) := by
    have ha : (tripleCharges (sourceA2722 + difference 4 0) (sourceB2722 + difference 0 4) sourceC2722) = raw37635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2722 sourceB2722 sourceC2722 difference raw37635; decide +kernel
    rw [ha]
    exact (canonical37635 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2722 + difference 5 0) (sourceB2722 + difference 0 5) sourceC2722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 767) := by
    have ha : (tripleCharges (sourceA2722 + difference 5 0) (sourceB2722 + difference 0 5) sourceC2722) = raw37636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2722 sourceB2722 sourceC2722 difference raw37636; decide +kernel
    rw [ha]
    exact (canonical37636 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2722 + sourceB2722) sourceC2722) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (doubleCharges (sourceA2722 + sourceB2722) sourceC2722) = raw37621 := by
      apply Matrix.ext; unfold doubleCharges sourceA2722 sourceB2722 sourceC2722 raw37621; decide +kernel
    rw [ha]
    exact (canonical37621 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2722 sourceB2722 sourceC2722
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2722, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2723 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2723 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2723 : Charge := ![-4, -1, 0, 1, 1, 3]
def sourceForm2723 : Integer.Sparse Master := [(Sum.inr 767, 1), (Sum.inr 1571, 1), (Sum.inr 1588, 1), (Sum.inr 1674, 2), (Sum.inr 1690, 1), (Sum.inr 4064, -1)]

theorem sourceEq2723 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2723 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2723 + difference 5 0) (sourceB2723 + difference 0 5) sourceC2723) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 767) := by
    have ha : (tripleCharges (sourceA2723 + difference 5 0) (sourceB2723 + difference 0 5) sourceC2723) = raw37636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2723 sourceB2723 sourceC2723 difference raw37636; decide +kernel
    rw [ha]
    exact (canonical37636 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2723 + difference 5 1) (sourceB2723 + difference 1 5) sourceC2723) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1571) := by
    have ha : (tripleCharges (sourceA2723 + difference 5 1) (sourceB2723 + difference 1 5) sourceC2723) = raw37637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2723 sourceB2723 sourceC2723 difference raw37637; decide +kernel
    rw [ha]
    exact (canonical37637 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2723 + difference 5 2) (sourceB2723 + difference 2 5) sourceC2723) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1588) := by
    have ha : (tripleCharges (sourceA2723 + difference 5 2) (sourceB2723 + difference 2 5) sourceC2723) = raw37638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2723 sourceB2723 sourceC2723 difference raw37638; decide +kernel
    rw [ha]
    exact (canonical37638 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2723 + difference 5 3) (sourceB2723 + difference 3 5) sourceC2723) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA2723 + difference 5 3) (sourceB2723 + difference 3 5) sourceC2723) = raw37639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2723 sourceB2723 sourceC2723 difference raw37639; decide +kernel
    rw [ha]
    exact (canonical37639 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2723 + difference 5 4) (sourceB2723 + difference 4 5) sourceC2723) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA2723 + difference 5 4) (sourceB2723 + difference 4 5) sourceC2723) = raw37640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2723 sourceB2723 sourceC2723 difference raw37640; decide +kernel
    rw [ha]
    exact (canonical37640 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2723 + difference 5 5) (sourceB2723 + difference 5 5) sourceC2723) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1690) := by
    have ha : (tripleCharges (sourceA2723 + difference 5 5) (sourceB2723 + difference 5 5) sourceC2723) = raw37617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2723 sourceB2723 sourceC2723 difference raw37617; decide +kernel
    rw [ha]
    exact (canonical37617 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2723 + sourceB2723) sourceC2723) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (doubleCharges (sourceA2723 + sourceB2723) sourceC2723) = raw37621 := by
      apply Matrix.ext; unfold doubleCharges sourceA2723 sourceB2723 sourceC2723 raw37621; decide +kernel
    rw [ha]
    exact (canonical37621 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2723 sourceB2723 sourceC2723
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2723, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2724 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB2724 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2724 : Charge := ![-4, -1, 0, 1, 2, 2]
def sourceForm2724 : Integer.Sparse Master := [(Sum.inr 761, 1), (Sum.inr 1567, 1), (Sum.inr 1671, 1), (Sum.inr 1678, 2), (Sum.inr 1691, 1), (Sum.inr 4065, -1)]

theorem sourceEq2724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2724 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2724 + difference 3 0) (sourceB2724 + difference 0 3) sourceC2724) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 761) := by
    have ha : (tripleCharges (sourceA2724 + difference 3 0) (sourceB2724 + difference 0 3) sourceC2724) = raw37641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2724 sourceB2724 sourceC2724 difference raw37641; decide +kernel
    rw [ha]
    exact (canonical37641 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2724 + difference 3 1) (sourceB2724 + difference 1 3) sourceC2724) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1567) := by
    have ha : (tripleCharges (sourceA2724 + difference 3 1) (sourceB2724 + difference 1 3) sourceC2724) = raw37642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2724 sourceB2724 sourceC2724 difference raw37642; decide +kernel
    rw [ha]
    exact (canonical37642 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2724 + difference 3 2) (sourceB2724 + difference 2 3) sourceC2724) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1691) := by
    have ha : (tripleCharges (sourceA2724 + difference 3 2) (sourceB2724 + difference 2 3) sourceC2724) = raw37643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2724 sourceB2724 sourceC2724 difference raw37643; decide +kernel
    rw [ha]
    exact (canonical37643 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2724 + difference 3 3) (sourceB2724 + difference 3 3) sourceC2724) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1671) := by
    have ha : (tripleCharges (sourceA2724 + difference 3 3) (sourceB2724 + difference 3 3) sourceC2724) = raw37644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2724 sourceB2724 sourceC2724 difference raw37644; decide +kernel
    rw [ha]
    exact (canonical37644 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2724 + difference 3 4) (sourceB2724 + difference 4 3) sourceC2724) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2724 + difference 3 4) (sourceB2724 + difference 4 3) sourceC2724) = raw37645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2724 sourceB2724 sourceC2724 difference raw37645; decide +kernel
    rw [ha]
    exact (canonical37645 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2724 + difference 3 5) (sourceB2724 + difference 5 3) sourceC2724) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2724 + difference 3 5) (sourceB2724 + difference 5 3) sourceC2724) = raw37646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2724 sourceB2724 sourceC2724 difference raw37646; decide +kernel
    rw [ha]
    exact (canonical37646 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2724 + sourceB2724) sourceC2724) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (doubleCharges (sourceA2724 + sourceB2724) sourceC2724) = raw37647 := by
      apply Matrix.ext; unfold doubleCharges sourceA2724 sourceB2724 sourceC2724 raw37647; decide +kernel
    rw [ha]
    exact (canonical37647 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2724 sourceB2724 sourceC2724
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2724, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2725 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceB2725 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2725 : Charge := ![-4, -1, 0, 1, 2, 2]
def sourceForm2725 : Integer.Sparse Master := [(Sum.inr 1681, 1), (Sum.inr 2657, 1), (Sum.inr 3258, 1), (Sum.inr 3265, 1), (Sum.inr 3270, 2), (Sum.inr 4065, -1)]

theorem sourceEq2725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2725 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2725 + difference 0 5) (sourceB2725 + difference 5 0) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA2725 + difference 0 5) (sourceB2725 + difference 5 0) sourceC2725) = raw37648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37648; decide +kernel
    rw [ha]
    exact (canonical37648 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2725 + difference 1 5) (sourceB2725 + difference 5 1) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3270) := by
    have ha : (tripleCharges (sourceA2725 + difference 1 5) (sourceB2725 + difference 5 1) sourceC2725) = raw37649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37649; decide +kernel
    rw [ha]
    exact (canonical37649 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2725 + difference 2 5) (sourceB2725 + difference 5 2) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA2725 + difference 2 5) (sourceB2725 + difference 5 2) sourceC2725) = raw37650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37650; decide +kernel
    rw [ha]
    exact (canonical37650 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2725 + difference 3 5) (sourceB2725 + difference 5 3) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3270) := by
    have ha : (tripleCharges (sourceA2725 + difference 3 5) (sourceB2725 + difference 5 3) sourceC2725) = raw37651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37651; decide +kernel
    rw [ha]
    exact (canonical37651 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2725 + difference 4 5) (sourceB2725 + difference 5 4) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA2725 + difference 4 5) (sourceB2725 + difference 5 4) sourceC2725) = raw37652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37652; decide +kernel
    rw [ha]
    exact (canonical37652 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2725 + difference 5 5) (sourceB2725 + difference 5 5) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2725 + difference 5 5) (sourceB2725 + difference 5 5) sourceC2725) = raw37653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37653; decide +kernel
    rw [ha]
    exact (canonical37653 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2725 + sourceB2725) sourceC2725) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (doubleCharges (sourceA2725 + sourceB2725) sourceC2725) = raw37647 := by
      apply Matrix.ext; unfold doubleCharges sourceA2725 sourceB2725 sourceC2725 raw37647; decide +kernel
    rw [ha]
    exact (canonical37647 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2725 sourceB2725 sourceC2725
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2725, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2726 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2726 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC2726 : Charge := ![-4, -1, 0, 1, 2, 2]
def sourceForm2726 : Integer.Sparse Master := [(Sum.inr 1691, 1), (Sum.inr 3261, 1), (Sum.inr 3265, 2), (Sum.inr 3274, 2), (Sum.inr 4065, -1)]

theorem sourceEq2726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2726 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2726 + difference 0 2) (sourceB2726 + difference 2 0) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1691) := by
    have ha : (tripleCharges (sourceA2726 + difference 0 2) (sourceB2726 + difference 2 0) sourceC2726) = raw37654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37654; decide +kernel
    rw [ha]
    exact (canonical37654 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2726 + difference 1 2) (sourceB2726 + difference 2 1) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3274) := by
    have ha : (tripleCharges (sourceA2726 + difference 1 2) (sourceB2726 + difference 2 1) sourceC2726) = raw37655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37655; decide +kernel
    rw [ha]
    exact (canonical37655 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2726 + difference 2 2) (sourceB2726 + difference 2 2) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA2726 + difference 2 2) (sourceB2726 + difference 2 2) sourceC2726) = raw37656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37656; decide +kernel
    rw [ha]
    exact (canonical37656 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2726 + difference 3 2) (sourceB2726 + difference 2 3) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3274) := by
    have ha : (tripleCharges (sourceA2726 + difference 3 2) (sourceB2726 + difference 2 3) sourceC2726) = raw37657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37657; decide +kernel
    rw [ha]
    exact (canonical37657 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2726 + difference 4 2) (sourceB2726 + difference 2 4) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA2726 + difference 4 2) (sourceB2726 + difference 2 4) sourceC2726) = raw37658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37658; decide +kernel
    rw [ha]
    exact (canonical37658 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2726 + difference 5 2) (sourceB2726 + difference 2 5) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA2726 + difference 5 2) (sourceB2726 + difference 2 5) sourceC2726) = raw37652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37652; decide +kernel
    rw [ha]
    exact (canonical37652 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2726 + sourceB2726) sourceC2726) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (doubleCharges (sourceA2726 + sourceB2726) sourceC2726) = raw37647 := by
      apply Matrix.ext; unfold doubleCharges sourceA2726 sourceB2726 sourceC2726 raw37647; decide +kernel
    rw [ha]
    exact (canonical37647 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2726 sourceB2726 sourceC2726
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2726, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2727 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2727 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2727 : Charge := ![-4, -1, 0, 1, 2, 2]
def sourceForm2727 : Integer.Sparse Master := [(Sum.inr 754, 1), (Sum.inr 757, 1), (Sum.inr 758, 1), (Sum.inr 768, 1), (Sum.inr 819, 1), (Sum.inr 1681, 1), (Sum.inr 4065, -1)]

theorem sourceEq2727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2727 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2727 + difference 0 0) (sourceB2727 + difference 0 0) sourceC2727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA2727 + difference 0 0) (sourceB2727 + difference 0 0) sourceC2727) = raw37659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2727 sourceB2727 sourceC2727 difference raw37659; decide +kernel
    rw [ha]
    exact (canonical37659 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2727 + difference 1 0) (sourceB2727 + difference 0 1) sourceC2727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 819) := by
    have ha : (tripleCharges (sourceA2727 + difference 1 0) (sourceB2727 + difference 0 1) sourceC2727) = raw37660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2727 sourceB2727 sourceC2727 difference raw37660; decide +kernel
    rw [ha]
    exact (canonical37660 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2727 + difference 2 0) (sourceB2727 + difference 0 2) sourceC2727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 754) := by
    have ha : (tripleCharges (sourceA2727 + difference 2 0) (sourceB2727 + difference 0 2) sourceC2727) = raw37661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2727 sourceB2727 sourceC2727 difference raw37661; decide +kernel
    rw [ha]
    exact (canonical37661 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2727 + difference 3 0) (sourceB2727 + difference 0 3) sourceC2727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 758) := by
    have ha : (tripleCharges (sourceA2727 + difference 3 0) (sourceB2727 + difference 0 3) sourceC2727) = raw37662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2727 sourceB2727 sourceC2727 difference raw37662; decide +kernel
    rw [ha]
    exact (canonical37662 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2727 + difference 4 0) (sourceB2727 + difference 0 4) sourceC2727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 757) := by
    have ha : (tripleCharges (sourceA2727 + difference 4 0) (sourceB2727 + difference 0 4) sourceC2727) = raw37663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2727 sourceB2727 sourceC2727 difference raw37663; decide +kernel
    rw [ha]
    exact (canonical37663 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2727 + difference 5 0) (sourceB2727 + difference 0 5) sourceC2727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 768) := by
    have ha : (tripleCharges (sourceA2727 + difference 5 0) (sourceB2727 + difference 0 5) sourceC2727) = raw37664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2727 sourceB2727 sourceC2727 difference raw37664; decide +kernel
    rw [ha]
    exact (canonical37664 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2727 + sourceB2727) sourceC2727) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (doubleCharges (sourceA2727 + sourceB2727) sourceC2727) = raw37647 := by
      apply Matrix.ext; unfold doubleCharges sourceA2727 sourceB2727 sourceC2727 raw37647; decide +kernel
    rw [ha]
    exact (canonical37647 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2727 sourceB2727 sourceC2727
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2727, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2728 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceB2728 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC2728 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2728 : Integer.Sparse Master := [(Sum.inr 2161, 2), (Sum.inr 2163, 2), (Sum.inr 2169, 2), (Sum.inr 4076, -1)]

theorem sourceEq2728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2728 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2728 + difference 0 4) (sourceB2728 + difference 4 0) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2728 + difference 0 4) (sourceB2728 + difference 4 0) sourceC2728) = raw37665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37665; decide +kernel
    rw [ha]
    exact (canonical37665 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2728 + difference 1 4) (sourceB2728 + difference 4 1) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2163) := by
    have ha : (tripleCharges (sourceA2728 + difference 1 4) (sourceB2728 + difference 4 1) sourceC2728) = raw37666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37666; decide +kernel
    rw [ha]
    exact (canonical37666 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2728 + difference 2 4) (sourceB2728 + difference 4 2) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2161) := by
    have ha : (tripleCharges (sourceA2728 + difference 2 4) (sourceB2728 + difference 4 2) sourceC2728) = raw37667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37667; decide +kernel
    rw [ha]
    exact (canonical37667 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2728 + difference 3 4) (sourceB2728 + difference 4 3) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2161) := by
    have ha : (tripleCharges (sourceA2728 + difference 3 4) (sourceB2728 + difference 4 3) sourceC2728) = raw37668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37668; decide +kernel
    rw [ha]
    exact (canonical37668 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2728 + difference 4 4) (sourceB2728 + difference 4 4) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2163) := by
    have ha : (tripleCharges (sourceA2728 + difference 4 4) (sourceB2728 + difference 4 4) sourceC2728) = raw37669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37669; decide +kernel
    rw [ha]
    exact (canonical37669 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2728 + difference 5 4) (sourceB2728 + difference 4 5) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2728 + difference 5 4) (sourceB2728 + difference 4 5) sourceC2728) = raw37670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37670; decide +kernel
    rw [ha]
    exact (canonical37670 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2728 + sourceB2728) sourceC2728) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2728 + sourceB2728) sourceC2728) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2728 sourceB2728 sourceC2728 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2728 sourceB2728 sourceC2728
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2728, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2729 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2729 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2729 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2729 : Integer.Sparse Master := [(Sum.inr 2155, 2), (Sum.inr 2159, 1), (Sum.inr 2168, 1), (Sum.inr 2273, 1), (Sum.inr 3596, 1), (Sum.inr 4076, -1)]

theorem sourceEq2729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2729 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2729 + difference 0 3) (sourceB2729 + difference 3 0) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3596) := by
    have ha : (tripleCharges (sourceA2729 + difference 0 3) (sourceB2729 + difference 3 0) sourceC2729) = raw37672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37672; decide +kernel
    rw [ha]
    exact (canonical37672 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2729 + difference 1 3) (sourceB2729 + difference 3 1) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2273) := by
    have ha : (tripleCharges (sourceA2729 + difference 1 3) (sourceB2729 + difference 3 1) sourceC2729) = raw37673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37673; decide +kernel
    rw [ha]
    exact (canonical37673 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2729 + difference 2 3) (sourceB2729 + difference 3 2) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2155) := by
    have ha : (tripleCharges (sourceA2729 + difference 2 3) (sourceB2729 + difference 3 2) sourceC2729) = raw37674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37674; decide +kernel
    rw [ha]
    exact (canonical37674 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2729 + difference 3 3) (sourceB2729 + difference 3 3) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2155) := by
    have ha : (tripleCharges (sourceA2729 + difference 3 3) (sourceB2729 + difference 3 3) sourceC2729) = raw37675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37675; decide +kernel
    rw [ha]
    exact (canonical37675 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2729 + difference 4 3) (sourceB2729 + difference 3 4) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2729 + difference 4 3) (sourceB2729 + difference 3 4) sourceC2729) = raw37676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37676; decide +kernel
    rw [ha]
    exact (canonical37676 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2729 + difference 5 3) (sourceB2729 + difference 3 5) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2159) := by
    have ha : (tripleCharges (sourceA2729 + difference 5 3) (sourceB2729 + difference 3 5) sourceC2729) = raw37677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37677; decide +kernel
    rw [ha]
    exact (canonical37677 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2729 + sourceB2729) sourceC2729) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2729 + sourceB2729) sourceC2729) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2729 sourceB2729 sourceC2729 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2729 sourceB2729 sourceC2729
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2729, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2730 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB2730 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2730 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2730 : Integer.Sparse Master := [(Sum.inr 2164, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2286, 1), (Sum.inr 3423, 1), (Sum.inr 4076, -1)]

theorem sourceEq2730 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2730 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2730 + difference 0 3) (sourceB2730 + difference 3 0) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2730 + difference 0 3) (sourceB2730 + difference 3 0) sourceC2730) = raw37678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37678; decide +kernel
    rw [ha]
    exact (canonical37678 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2730 + difference 1 3) (sourceB2730 + difference 3 1) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA2730 + difference 1 3) (sourceB2730 + difference 3 1) sourceC2730) = raw37679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37679; decide +kernel
    rw [ha]
    exact (canonical37679 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2730 + difference 2 3) (sourceB2730 + difference 3 2) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2730 + difference 2 3) (sourceB2730 + difference 3 2) sourceC2730) = raw37680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37680; decide +kernel
    rw [ha]
    exact (canonical37680 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2730 + difference 3 3) (sourceB2730 + difference 3 3) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2730 + difference 3 3) (sourceB2730 + difference 3 3) sourceC2730) = raw37681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37681; decide +kernel
    rw [ha]
    exact (canonical37681 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2730 + difference 4 3) (sourceB2730 + difference 3 4) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2730 + difference 4 3) (sourceB2730 + difference 3 4) sourceC2730) = raw37670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37670; decide +kernel
    rw [ha]
    exact (canonical37670 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2730 + difference 5 3) (sourceB2730 + difference 3 5) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2730 + difference 5 3) (sourceB2730 + difference 3 5) sourceC2730) = raw37676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37676; decide +kernel
    rw [ha]
    exact (canonical37676 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2730 + sourceB2730) sourceC2730) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2730 + sourceB2730) sourceC2730) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2730 sourceB2730 sourceC2730 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2730 sourceB2730 sourceC2730
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2730, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2731 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2731 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC2731 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2731 : Integer.Sparse Master := [(Sum.inr 2168, 1), (Sum.inr 3415, 2), (Sum.inr 3422, 1), (Sum.inr 3423, 1), (Sum.inr 3596, 1), (Sum.inr 4076, -1)]

theorem sourceEq2731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2731 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2731 + difference 0 3) (sourceB2731 + difference 3 0) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2731 + difference 0 3) (sourceB2731 + difference 3 0) sourceC2731) = raw37682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37682; decide +kernel
    rw [ha]
    exact (canonical37682 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2731 + difference 1 3) (sourceB2731 + difference 3 1) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3596) := by
    have ha : (tripleCharges (sourceA2731 + difference 1 3) (sourceB2731 + difference 3 1) sourceC2731) = raw37672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37672; decide +kernel
    rw [ha]
    exact (canonical37672 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2731 + difference 2 3) (sourceB2731 + difference 3 2) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2731 + difference 2 3) (sourceB2731 + difference 3 2) sourceC2731) = raw37683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37683; decide +kernel
    rw [ha]
    exact (canonical37683 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2731 + difference 3 3) (sourceB2731 + difference 3 3) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2731 + difference 3 3) (sourceB2731 + difference 3 3) sourceC2731) = raw37684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37684; decide +kernel
    rw [ha]
    exact (canonical37684 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2731 + difference 4 3) (sourceB2731 + difference 3 4) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2731 + difference 4 3) (sourceB2731 + difference 3 4) sourceC2731) = raw37685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37685; decide +kernel
    rw [ha]
    exact (canonical37685 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2731 + difference 5 3) (sourceB2731 + difference 3 5) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2731 + difference 5 3) (sourceB2731 + difference 3 5) sourceC2731) = raw37686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37686; decide +kernel
    rw [ha]
    exact (canonical37686 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2731 + sourceB2731) sourceC2731) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2731 + sourceB2731) sourceC2731) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2731 sourceB2731 sourceC2731 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2731 sourceB2731 sourceC2731
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2731, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2732 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB2732 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC2732 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2732 : Integer.Sparse Master := [(Sum.inr 3419, 2), (Sum.inr 3422, 2), (Sum.inr 3423, 2), (Sum.inr 4076, -1)]

theorem sourceEq2732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2732 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2732 + difference 0 3) (sourceB2732 + difference 3 0) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2732 + difference 0 3) (sourceB2732 + difference 3 0) sourceC2732) = raw37687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37687; decide +kernel
    rw [ha]
    exact (canonical37687 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2732 + difference 1 3) (sourceB2732 + difference 3 1) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2732 + difference 1 3) (sourceB2732 + difference 3 1) sourceC2732) = raw37678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37678; decide +kernel
    rw [ha]
    exact (canonical37678 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2732 + difference 2 3) (sourceB2732 + difference 3 2) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2732 + difference 2 3) (sourceB2732 + difference 3 2) sourceC2732) = raw37688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37688; decide +kernel
    rw [ha]
    exact (canonical37688 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2732 + difference 3 3) (sourceB2732 + difference 3 3) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2732 + difference 3 3) (sourceB2732 + difference 3 3) sourceC2732) = raw37689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37689; decide +kernel
    rw [ha]
    exact (canonical37689 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2732 + difference 4 3) (sourceB2732 + difference 3 4) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2732 + difference 4 3) (sourceB2732 + difference 3 4) sourceC2732) = raw37690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37690; decide +kernel
    rw [ha]
    exact (canonical37690 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2732 + difference 5 3) (sourceB2732 + difference 3 5) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2732 + difference 5 3) (sourceB2732 + difference 3 5) sourceC2732) = raw37685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37685; decide +kernel
    rw [ha]
    exact (canonical37685 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2732 + sourceB2732) sourceC2732) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2732 + sourceB2732) sourceC2732) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2732 sourceB2732 sourceC2732 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2732 sourceB2732 sourceC2732
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2732, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2733 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceB2733 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC2733 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2733 : Integer.Sparse Master := [(Sum.inr 2169, 2), (Sum.inr 3423, 2), (Sum.inr 3512, 2), (Sum.inr 4076, -1)]

theorem sourceEq2733 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2733 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 0) (sourceB2733 + difference 0 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 0) (sourceB2733 + difference 0 2) sourceC2733) = raw37670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37670; decide +kernel
    rw [ha]
    exact (canonical37670 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 1) (sourceB2733 + difference 1 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 1) (sourceB2733 + difference 1 2) sourceC2733) = raw37690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37690; decide +kernel
    rw [ha]
    exact (canonical37690 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 2) (sourceB2733 + difference 2 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3512) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 2) (sourceB2733 + difference 2 2) sourceC2733) = raw37691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37691; decide +kernel
    rw [ha]
    exact (canonical37691 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 3) (sourceB2733 + difference 3 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3512) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 3) (sourceB2733 + difference 3 2) sourceC2733) = raw37692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37692; decide +kernel
    rw [ha]
    exact (canonical37692 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 4) (sourceB2733 + difference 4 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 4) (sourceB2733 + difference 4 2) sourceC2733) = raw37678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37678; decide +kernel
    rw [ha]
    exact (canonical37678 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 5) (sourceB2733 + difference 5 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 5) (sourceB2733 + difference 5 2) sourceC2733) = raw37665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37665; decide +kernel
    rw [ha]
    exact (canonical37665 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2733 + sourceB2733) sourceC2733) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2733 + sourceB2733) sourceC2733) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2733 sourceB2733 sourceC2733 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2733 sourceB2733 sourceC2733
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2733, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2734 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceB2734 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2734 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2734 : Integer.Sparse Master := [(Sum.inr 2369, 1), (Sum.inr 3326, 2), (Sum.inr 3331, 1), (Sum.inr 3423, 1), (Sum.inr 3596, 1), (Sum.inr 4076, -1)]

theorem sourceEq2734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2734 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2734 + difference 0 0) (sourceB2734 + difference 0 0) sourceC2734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3596) := by
    have ha : (tripleCharges (sourceA2734 + difference 0 0) (sourceB2734 + difference 0 0) sourceC2734) = raw37672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2734 sourceB2734 sourceC2734 difference raw37672; decide +kernel
    rw [ha]
    exact (canonical37672 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2734 + difference 0 1) (sourceB2734 + difference 1 0) sourceC2734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2734 + difference 0 1) (sourceB2734 + difference 1 0) sourceC2734) = raw37682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2734 sourceB2734 sourceC2734 difference raw37682; decide +kernel
    rw [ha]
    exact (canonical37682 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2734 + difference 0 2) (sourceB2734 + difference 2 0) sourceC2734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3326) := by
    have ha : (tripleCharges (sourceA2734 + difference 0 2) (sourceB2734 + difference 2 0) sourceC2734) = raw37693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2734 sourceB2734 sourceC2734 difference raw37693; decide +kernel
    rw [ha]
    exact (canonical37693 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2734 + difference 0 3) (sourceB2734 + difference 3 0) sourceC2734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3326) := by
    have ha : (tripleCharges (sourceA2734 + difference 0 3) (sourceB2734 + difference 3 0) sourceC2734) = raw37694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2734 sourceB2734 sourceC2734 difference raw37694; decide +kernel
    rw [ha]
    exact (canonical37694 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2734 + difference 0 4) (sourceB2734 + difference 4 0) sourceC2734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2369) := by
    have ha : (tripleCharges (sourceA2734 + difference 0 4) (sourceB2734 + difference 4 0) sourceC2734) = raw37695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2734 sourceB2734 sourceC2734 difference raw37695; decide +kernel
    rw [ha]
    exact (canonical37695 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2734 + difference 0 5) (sourceB2734 + difference 5 0) sourceC2734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3331) := by
    have ha : (tripleCharges (sourceA2734 + difference 0 5) (sourceB2734 + difference 5 0) sourceC2734) = raw37696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2734 sourceB2734 sourceC2734 difference raw37696; decide +kernel
    rw [ha]
    exact (canonical37696 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2734 + sourceB2734) sourceC2734) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2734 + sourceB2734) sourceC2734) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2734 sourceB2734 sourceC2734 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2734 sourceB2734 sourceC2734
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2734, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2735 : Charge := ![1, 2, 0, 0, -1, -2]
def sourceB2735 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2735 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2735 : Integer.Sparse Master := [(Sum.inr 1859, 1), (Sum.inr 3325, 2), (Sum.inr 3331, 1), (Sum.inr 3422, 1), (Sum.inr 3423, 1), (Sum.inr 4076, -1)]

theorem sourceEq2735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2735 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2735 + difference 0 0) (sourceB2735 + difference 0 0) sourceC2735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2735 + difference 0 0) (sourceB2735 + difference 0 0) sourceC2735) = raw37678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2735 sourceB2735 sourceC2735 difference raw37678; decide +kernel
    rw [ha]
    exact (canonical37678 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2735 + difference 0 1) (sourceB2735 + difference 1 0) sourceC2735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2735 + difference 0 1) (sourceB2735 + difference 1 0) sourceC2735) = raw37687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2735 sourceB2735 sourceC2735 difference raw37687; decide +kernel
    rw [ha]
    exact (canonical37687 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2735 + difference 0 2) (sourceB2735 + difference 2 0) sourceC2735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3325) := by
    have ha : (tripleCharges (sourceA2735 + difference 0 2) (sourceB2735 + difference 2 0) sourceC2735) = raw37697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2735 sourceB2735 sourceC2735 difference raw37697; decide +kernel
    rw [ha]
    exact (canonical37697 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2735 + difference 0 3) (sourceB2735 + difference 3 0) sourceC2735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3325) := by
    have ha : (tripleCharges (sourceA2735 + difference 0 3) (sourceB2735 + difference 3 0) sourceC2735) = raw37698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2735 sourceB2735 sourceC2735 difference raw37698; decide +kernel
    rw [ha]
    exact (canonical37698 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2735 + difference 0 4) (sourceB2735 + difference 4 0) sourceC2735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3331) := by
    have ha : (tripleCharges (sourceA2735 + difference 0 4) (sourceB2735 + difference 4 0) sourceC2735) = raw37696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2735 sourceB2735 sourceC2735 difference raw37696; decide +kernel
    rw [ha]
    exact (canonical37696 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2735 + difference 0 5) (sourceB2735 + difference 5 0) sourceC2735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1859) := by
    have ha : (tripleCharges (sourceA2735 + difference 0 5) (sourceB2735 + difference 5 0) sourceC2735) = raw37699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2735 sourceB2735 sourceC2735 difference raw37699; decide +kernel
    rw [ha]
    exact (canonical37699 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2735 + sourceB2735) sourceC2735) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2735 + sourceB2735) sourceC2735) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2735 sourceB2735 sourceC2735 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2735 sourceB2735 sourceC2735
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2735, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2736 : Charge := ![1, 2, 0, 0, -1, -2]
def sourceB2736 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2736 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2736 : Integer.Sparse Master := [(Sum.inr 1851, 2), (Sum.inr 1857, 1), (Sum.inr 1859, 1), (Sum.inr 2169, 1), (Sum.inr 3423, 1), (Sum.inr 4076, -1)]

theorem sourceEq2736 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2736 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2736 + difference 0 5) (sourceB2736 + difference 5 0) sourceC2736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1859) := by
    have ha : (tripleCharges (sourceA2736 + difference 0 5) (sourceB2736 + difference 5 0) sourceC2736) = raw37699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2736 sourceB2736 sourceC2736 difference raw37699; decide +kernel
    rw [ha]
    exact (canonical37699 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2736 + difference 1 5) (sourceB2736 + difference 5 1) sourceC2736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1857) := by
    have ha : (tripleCharges (sourceA2736 + difference 1 5) (sourceB2736 + difference 5 1) sourceC2736) = raw37700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2736 sourceB2736 sourceC2736 difference raw37700; decide +kernel
    rw [ha]
    exact (canonical37700 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2736 + difference 2 5) (sourceB2736 + difference 5 2) sourceC2736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1851) := by
    have ha : (tripleCharges (sourceA2736 + difference 2 5) (sourceB2736 + difference 5 2) sourceC2736) = raw37701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2736 sourceB2736 sourceC2736 difference raw37701; decide +kernel
    rw [ha]
    exact (canonical37701 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2736 + difference 3 5) (sourceB2736 + difference 5 3) sourceC2736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1851) := by
    have ha : (tripleCharges (sourceA2736 + difference 3 5) (sourceB2736 + difference 5 3) sourceC2736) = raw37702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2736 sourceB2736 sourceC2736 difference raw37702; decide +kernel
    rw [ha]
    exact (canonical37702 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2736 + difference 4 5) (sourceB2736 + difference 5 4) sourceC2736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2736 + difference 4 5) (sourceB2736 + difference 5 4) sourceC2736) = raw37665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2736 sourceB2736 sourceC2736 difference raw37665; decide +kernel
    rw [ha]
    exact (canonical37665 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2736 + difference 5 5) (sourceB2736 + difference 5 5) sourceC2736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2736 + difference 5 5) (sourceB2736 + difference 5 5) sourceC2736) = raw37678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2736 sourceB2736 sourceC2736 difference raw37678; decide +kernel
    rw [ha]
    exact (canonical37678 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2736 + sourceB2736) sourceC2736) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2736 + sourceB2736) sourceC2736) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2736 sourceB2736 sourceC2736 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2736 sourceB2736 sourceC2736
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2736, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2737 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceB2737 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2737 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2737 : Integer.Sparse Master := [(Sum.inr 963, 1), (Sum.inr 1859, 1), (Sum.inr 1984, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 4076, -1)]

theorem sourceEq2737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2737 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2737 + difference 0 0) (sourceB2737 + difference 0 0) sourceC2737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2737 + difference 0 0) (sourceB2737 + difference 0 0) sourceC2737) = raw37665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2737 sourceB2737 sourceC2737 difference raw37665; decide +kernel
    rw [ha]
    exact (canonical37665 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2737 + difference 0 1) (sourceB2737 + difference 1 0) sourceC2737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2737 + difference 0 1) (sourceB2737 + difference 1 0) sourceC2737) = raw37703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2737 sourceB2737 sourceC2737 difference raw37703; decide +kernel
    rw [ha]
    exact (canonical37703 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2737 + difference 0 2) (sourceB2737 + difference 2 0) sourceC2737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1984) := by
    have ha : (tripleCharges (sourceA2737 + difference 0 2) (sourceB2737 + difference 2 0) sourceC2737) = raw37704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2737 sourceB2737 sourceC2737 difference raw37704; decide +kernel
    rw [ha]
    exact (canonical37704 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2737 + difference 0 3) (sourceB2737 + difference 3 0) sourceC2737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1984) := by
    have ha : (tripleCharges (sourceA2737 + difference 0 3) (sourceB2737 + difference 3 0) sourceC2737) = raw37705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2737 sourceB2737 sourceC2737 difference raw37705; decide +kernel
    rw [ha]
    exact (canonical37705 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2737 + difference 0 4) (sourceB2737 + difference 4 0) sourceC2737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1859) := by
    have ha : (tripleCharges (sourceA2737 + difference 0 4) (sourceB2737 + difference 4 0) sourceC2737) = raw37699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2737 sourceB2737 sourceC2737 difference raw37699; decide +kernel
    rw [ha]
    exact (canonical37699 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2737 + difference 0 5) (sourceB2737 + difference 5 0) sourceC2737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 963) := by
    have ha : (tripleCharges (sourceA2737 + difference 0 5) (sourceB2737 + difference 5 0) sourceC2737) = raw37706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2737 sourceB2737 sourceC2737 difference raw37706; decide +kernel
    rw [ha]
    exact (canonical37706 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2737 + sourceB2737) sourceC2737) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2737 + sourceB2737) sourceC2737) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2737 sourceB2737 sourceC2737 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2737 sourceB2737 sourceC2737
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2737, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2738 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2738 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC2738 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2738 : Integer.Sparse Master := [(Sum.inr 1850, 2), (Sum.inr 1856, 1), (Sum.inr 1859, 1), (Sum.inr 2168, 1), (Sum.inr 3422, 1), (Sum.inr 4076, -1)]

theorem sourceEq2738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2738 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2738 + difference 0 0) (sourceB2738 + difference 0 0) sourceC2738) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2738 + difference 0 0) (sourceB2738 + difference 0 0) sourceC2738) = raw37685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2738 sourceB2738 sourceC2738 difference raw37685; decide +kernel
    rw [ha]
    exact (canonical37685 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2738 + difference 1 0) (sourceB2738 + difference 0 1) sourceC2738) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2738 + difference 1 0) (sourceB2738 + difference 0 1) sourceC2738) = raw37676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2738 sourceB2738 sourceC2738 difference raw37676; decide +kernel
    rw [ha]
    exact (canonical37676 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2738 + difference 2 0) (sourceB2738 + difference 0 2) sourceC2738) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1850) := by
    have ha : (tripleCharges (sourceA2738 + difference 2 0) (sourceB2738 + difference 0 2) sourceC2738) = raw37707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2738 sourceB2738 sourceC2738 difference raw37707; decide +kernel
    rw [ha]
    exact (canonical37707 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2738 + difference 3 0) (sourceB2738 + difference 0 3) sourceC2738) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1850) := by
    have ha : (tripleCharges (sourceA2738 + difference 3 0) (sourceB2738 + difference 0 3) sourceC2738) = raw37708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2738 sourceB2738 sourceC2738 difference raw37708; decide +kernel
    rw [ha]
    exact (canonical37708 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2738 + difference 4 0) (sourceB2738 + difference 0 4) sourceC2738) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1859) := by
    have ha : (tripleCharges (sourceA2738 + difference 4 0) (sourceB2738 + difference 0 4) sourceC2738) = raw37709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2738 sourceB2738 sourceC2738 difference raw37709; decide +kernel
    rw [ha]
    exact (canonical37709 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2738 + difference 5 0) (sourceB2738 + difference 0 5) sourceC2738) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1856) := by
    have ha : (tripleCharges (sourceA2738 + difference 5 0) (sourceB2738 + difference 0 5) sourceC2738) = raw37710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2738 sourceB2738 sourceC2738 difference raw37710; decide +kernel
    rw [ha]
    exact (canonical37710 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2738 + sourceB2738) sourceC2738) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2738 + sourceB2738) sourceC2738) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2738 sourceB2738 sourceC2738 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2738 sourceB2738 sourceC2738
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2738, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2739 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2739 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2739 : Charge := ![-3, -2, 0, 0, 2, 3]
def sourceForm2739 : Integer.Sparse Master := [(Sum.inr 962, 1), (Sum.inr 1843, 2), (Sum.inr 1856, 1), (Sum.inr 2159, 1), (Sum.inr 2168, 1), (Sum.inr 4076, -1)]

theorem sourceEq2739 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2739 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2739 + difference 0 0) (sourceB2739 + difference 0 0) sourceC2739) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2739 + difference 0 0) (sourceB2739 + difference 0 0) sourceC2739) = raw37686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2739 sourceB2739 sourceC2739 difference raw37686; decide +kernel
    rw [ha]
    exact (canonical37686 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2739 + difference 1 0) (sourceB2739 + difference 0 1) sourceC2739) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2159) := by
    have ha : (tripleCharges (sourceA2739 + difference 1 0) (sourceB2739 + difference 0 1) sourceC2739) = raw37677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2739 sourceB2739 sourceC2739 difference raw37677; decide +kernel
    rw [ha]
    exact (canonical37677 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2739 + difference 2 0) (sourceB2739 + difference 0 2) sourceC2739) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1843) := by
    have ha : (tripleCharges (sourceA2739 + difference 2 0) (sourceB2739 + difference 0 2) sourceC2739) = raw37711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2739 sourceB2739 sourceC2739 difference raw37711; decide +kernel
    rw [ha]
    exact (canonical37711 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2739 + difference 3 0) (sourceB2739 + difference 0 3) sourceC2739) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1843) := by
    have ha : (tripleCharges (sourceA2739 + difference 3 0) (sourceB2739 + difference 0 3) sourceC2739) = raw37712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2739 sourceB2739 sourceC2739 difference raw37712; decide +kernel
    rw [ha]
    exact (canonical37712 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2739 + difference 4 0) (sourceB2739 + difference 0 4) sourceC2739) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1856) := by
    have ha : (tripleCharges (sourceA2739 + difference 4 0) (sourceB2739 + difference 0 4) sourceC2739) = raw37710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2739 sourceB2739 sourceC2739 difference raw37710; decide +kernel
    rw [ha]
    exact (canonical37710 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2739 + difference 5 0) (sourceB2739 + difference 0 5) sourceC2739) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 962) := by
    have ha : (tripleCharges (sourceA2739 + difference 5 0) (sourceB2739 + difference 0 5) sourceC2739) = raw37713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2739 sourceB2739 sourceC2739 difference raw37713; decide +kernel
    rw [ha]
    exact (canonical37713 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2739 + sourceB2739) sourceC2739) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2739 + sourceB2739) sourceC2739) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2739 sourceB2739 sourceC2739 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2739 sourceB2739 sourceC2739
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2739, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2740 : Charge := ![0, 2, 0, -1, 1, -2]
def sourceB2740 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2740 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2740 : Integer.Sparse Master := [(Sum.inr 2147, 1), (Sum.inr 2151, 1), (Sum.inr 2153, 1), (Sum.inr 2165, 1), (Sum.inr 2256, 1), (Sum.inr 3457, 1), (Sum.inr 4074, -1)]

theorem sourceEq2740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2740 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2740 + difference 0 4) (sourceB2740 + difference 4 0) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2740 + difference 0 4) (sourceB2740 + difference 4 0) sourceC2740) = raw37714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37714; decide +kernel
    rw [ha]
    exact (canonical37714 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2740 + difference 1 4) (sourceB2740 + difference 4 1) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA2740 + difference 1 4) (sourceB2740 + difference 4 1) sourceC2740) = raw37715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37715; decide +kernel
    rw [ha]
    exact (canonical37715 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2740 + difference 2 4) (sourceB2740 + difference 4 2) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2147) := by
    have ha : (tripleCharges (sourceA2740 + difference 2 4) (sourceB2740 + difference 4 2) sourceC2740) = raw37716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37716; decide +kernel
    rw [ha]
    exact (canonical37716 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2740 + difference 3 4) (sourceB2740 + difference 4 3) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2165) := by
    have ha : (tripleCharges (sourceA2740 + difference 3 4) (sourceB2740 + difference 4 3) sourceC2740) = raw37717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37717; decide +kernel
    rw [ha]
    exact (canonical37717 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2740 + difference 4 4) (sourceB2740 + difference 4 4) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2740 + difference 4 4) (sourceB2740 + difference 4 4) sourceC2740) = raw37718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37718; decide +kernel
    rw [ha]
    exact (canonical37718 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2740 + difference 5 4) (sourceB2740 + difference 4 5) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2740 + difference 5 4) (sourceB2740 + difference 4 5) sourceC2740) = raw37719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37719; decide +kernel
    rw [ha]
    exact (canonical37719 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2740 + sourceB2740) sourceC2740) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2740 + sourceB2740) sourceC2740) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2740 sourceB2740 sourceC2740 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2740 sourceB2740 sourceC2740
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2740, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2741 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceB2741 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2741 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2741 : Integer.Sparse Master := [(Sum.inr 2160, 1), (Sum.inr 2162, 2), (Sum.inr 2165, 1), (Sum.inr 2180, 1), (Sum.inr 2186, 1), (Sum.inr 4074, -1)]

theorem sourceEq2741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2741 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2741 + difference 0 4) (sourceB2741 + difference 4 0) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2741 + difference 0 4) (sourceB2741 + difference 4 0) sourceC2741) = raw37721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37721; decide +kernel
    rw [ha]
    exact (canonical37721 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2741 + difference 1 4) (sourceB2741 + difference 4 1) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2180) := by
    have ha : (tripleCharges (sourceA2741 + difference 1 4) (sourceB2741 + difference 4 1) sourceC2741) = raw37722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37722; decide +kernel
    rw [ha]
    exact (canonical37722 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2741 + difference 2 4) (sourceB2741 + difference 4 2) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2160) := by
    have ha : (tripleCharges (sourceA2741 + difference 2 4) (sourceB2741 + difference 4 2) sourceC2741) = raw37723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37723; decide +kernel
    rw [ha]
    exact (canonical37723 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2741 + difference 3 4) (sourceB2741 + difference 4 3) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2741 + difference 3 4) (sourceB2741 + difference 4 3) sourceC2741) = raw37724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37724; decide +kernel
    rw [ha]
    exact (canonical37724 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2741 + difference 4 4) (sourceB2741 + difference 4 4) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2741 + difference 4 4) (sourceB2741 + difference 4 4) sourceC2741) = raw37725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37725; decide +kernel
    rw [ha]
    exact (canonical37725 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2741 + difference 5 4) (sourceB2741 + difference 4 5) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2165) := by
    have ha : (tripleCharges (sourceA2741 + difference 5 4) (sourceB2741 + difference 4 5) sourceC2741) = raw37717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37717; decide +kernel
    rw [ha]
    exact (canonical37717 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2741 + sourceB2741) sourceC2741) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2741 + sourceB2741) sourceC2741) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2741 sourceB2741 sourceC2741 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2741 sourceB2741 sourceC2741
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2741, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2742 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB2742 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2742 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2742 : Integer.Sparse Master := [(Sum.inr 2140, 1), (Sum.inr 2143, 1), (Sum.inr 2151, 2), (Sum.inr 2239, 1), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

theorem sourceEq2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2742 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2742 + difference 0 2) (sourceB2742 + difference 2 0) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2742 + difference 0 2) (sourceB2742 + difference 2 0) sourceC2742) = raw37726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37726; decide +kernel
    rw [ha]
    exact (canonical37726 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2742 + difference 1 2) (sourceB2742 + difference 2 1) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2239) := by
    have ha : (tripleCharges (sourceA2742 + difference 1 2) (sourceB2742 + difference 2 1) sourceC2742) = raw37727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37727; decide +kernel
    rw [ha]
    exact (canonical37727 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2742 + difference 2 2) (sourceB2742 + difference 2 2) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2140) := by
    have ha : (tripleCharges (sourceA2742 + difference 2 2) (sourceB2742 + difference 2 2) sourceC2742) = raw37728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37728; decide +kernel
    rw [ha]
    exact (canonical37728 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2742 + difference 3 2) (sourceB2742 + difference 2 3) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2742 + difference 3 2) (sourceB2742 + difference 2 3) sourceC2742) = raw37729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37729; decide +kernel
    rw [ha]
    exact (canonical37729 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2742 + difference 4 2) (sourceB2742 + difference 2 4) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2742 + difference 4 2) (sourceB2742 + difference 2 4) sourceC2742) = raw37719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37719; decide +kernel
    rw [ha]
    exact (canonical37719 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2742 + difference 5 2) (sourceB2742 + difference 2 5) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2742 + difference 5 2) (sourceB2742 + difference 2 5) sourceC2742) = raw37730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37730; decide +kernel
    rw [ha]
    exact (canonical37730 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2742 + sourceB2742) sourceC2742) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2742 + sourceB2742) sourceC2742) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2742 sourceB2742 sourceC2742 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2742 sourceB2742 sourceC2742
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2742, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2743 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceB2743 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC2743 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2743 : Integer.Sparse Master := [(Sum.inr 3408, 1), (Sum.inr 3411, 2), (Sum.inr 3413, 1), (Sum.inr 3420, 1), (Sum.inr 3457, 1), (Sum.inr 4074, -1)]

theorem sourceEq2743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2743 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2743 + difference 0 4) (sourceB2743 + difference 4 0) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2743 + difference 0 4) (sourceB2743 + difference 4 0) sourceC2743) = raw37731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37731; decide +kernel
    rw [ha]
    exact (canonical37731 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2743 + difference 1 4) (sourceB2743 + difference 4 1) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2743 + difference 1 4) (sourceB2743 + difference 4 1) sourceC2743) = raw37714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37714; decide +kernel
    rw [ha]
    exact (canonical37714 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2743 + difference 2 4) (sourceB2743 + difference 4 2) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2743 + difference 2 4) (sourceB2743 + difference 4 2) sourceC2743) = raw37732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37732; decide +kernel
    rw [ha]
    exact (canonical37732 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2743 + difference 3 4) (sourceB2743 + difference 4 3) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2743 + difference 3 4) (sourceB2743 + difference 4 3) sourceC2743) = raw37733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37733; decide +kernel
    rw [ha]
    exact (canonical37733 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2743 + difference 4 4) (sourceB2743 + difference 4 4) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2743 + difference 4 4) (sourceB2743 + difference 4 4) sourceC2743) = raw37734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37734; decide +kernel
    rw [ha]
    exact (canonical37734 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2743 + difference 5 4) (sourceB2743 + difference 4 5) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2743 + difference 5 4) (sourceB2743 + difference 4 5) sourceC2743) = raw37735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37735; decide +kernel
    rw [ha]
    exact (canonical37735 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2743 + sourceB2743) sourceC2743) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2743 + sourceB2743) sourceC2743) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2743 sourceB2743 sourceC2743 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2743 sourceB2743 sourceC2743
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2743, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2744 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB2744 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC2744 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2744 : Integer.Sparse Master := [(Sum.inr 2181, 1), (Sum.inr 2185, 1), (Sum.inr 2186, 1), (Sum.inr 2223, 2), (Sum.inr 3420, 1), (Sum.inr 4074, -1)]

theorem sourceEq2744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2744 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2744 + difference 0 4) (sourceB2744 + difference 4 0) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2744 + difference 0 4) (sourceB2744 + difference 4 0) sourceC2744) = raw37736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37736; decide +kernel
    rw [ha]
    exact (canonical37736 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2744 + difference 1 4) (sourceB2744 + difference 4 1) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2744 + difference 1 4) (sourceB2744 + difference 4 1) sourceC2744) = raw37721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37721; decide +kernel
    rw [ha]
    exact (canonical37721 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2744 + difference 2 4) (sourceB2744 + difference 4 2) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2181) := by
    have ha : (tripleCharges (sourceA2744 + difference 2 4) (sourceB2744 + difference 4 2) sourceC2744) = raw37737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37737; decide +kernel
    rw [ha]
    exact (canonical37737 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2744 + difference 3 4) (sourceB2744 + difference 4 3) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2744 + difference 3 4) (sourceB2744 + difference 4 3) sourceC2744) = raw37738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37738; decide +kernel
    rw [ha]
    exact (canonical37738 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2744 + difference 4 4) (sourceB2744 + difference 4 4) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2744 + difference 4 4) (sourceB2744 + difference 4 4) sourceC2744) = raw37739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37739; decide +kernel
    rw [ha]
    exact (canonical37739 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2744 + difference 5 4) (sourceB2744 + difference 4 5) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2744 + difference 5 4) (sourceB2744 + difference 4 5) sourceC2744) = raw37733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37733; decide +kernel
    rw [ha]
    exact (canonical37733 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2744 + sourceB2744) sourceC2744) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2744 + sourceB2744) sourceC2744) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2744 sourceB2744 sourceC2744 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2744 sourceB2744 sourceC2744
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2744, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2745 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB2745 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC2745 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2745 : Integer.Sparse Master := [(Sum.inr 2185, 1), (Sum.inr 3403, 1), (Sum.inr 3411, 2), (Sum.inr 3420, 1), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

theorem sourceEq2745 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2745 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2745 + difference 0 2) (sourceB2745 + difference 2 0) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2745 + difference 0 2) (sourceB2745 + difference 2 0) sourceC2745) = raw37740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37740; decide +kernel
    rw [ha]
    exact (canonical37740 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2745 + difference 1 2) (sourceB2745 + difference 2 1) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2745 + difference 1 2) (sourceB2745 + difference 2 1) sourceC2745) = raw37726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37726; decide +kernel
    rw [ha]
    exact (canonical37726 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2745 + difference 2 2) (sourceB2745 + difference 2 2) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3403) := by
    have ha : (tripleCharges (sourceA2745 + difference 2 2) (sourceB2745 + difference 2 2) sourceC2745) = raw37741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37741; decide +kernel
    rw [ha]
    exact (canonical37741 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2745 + difference 3 2) (sourceB2745 + difference 2 3) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2745 + difference 3 2) (sourceB2745 + difference 2 3) sourceC2745) = raw37742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37742; decide +kernel
    rw [ha]
    exact (canonical37742 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2745 + difference 4 2) (sourceB2745 + difference 2 4) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2745 + difference 4 2) (sourceB2745 + difference 2 4) sourceC2745) = raw37735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37735; decide +kernel
    rw [ha]
    exact (canonical37735 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2745 + difference 5 2) (sourceB2745 + difference 2 5) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2745 + difference 5 2) (sourceB2745 + difference 2 5) sourceC2745) = raw37743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37743; decide +kernel
    rw [ha]
    exact (canonical37743 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2745 + sourceB2745) sourceC2745) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2745 + sourceB2745) sourceC2745) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2745 sourceB2745 sourceC2745 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2745 sourceB2745 sourceC2745
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2745, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2746 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB2746 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC2746 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2746 : Integer.Sparse Master := [(Sum.inr 1847, 1), (Sum.inr 2181, 1), (Sum.inr 3323, 1), (Sum.inr 3408, 2), (Sum.inr 3420, 1), (Sum.inr 4074, -1)]

theorem sourceEq2746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2746 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2746 + difference 3 0) (sourceB2746 + difference 0 3) sourceC2746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1847) := by
    have ha : (tripleCharges (sourceA2746 + difference 3 0) (sourceB2746 + difference 0 3) sourceC2746) = raw37744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2746 sourceB2746 sourceC2746 difference raw37744; decide +kernel
    rw [ha]
    exact (canonical37744 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2746 + difference 3 1) (sourceB2746 + difference 1 3) sourceC2746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3323) := by
    have ha : (tripleCharges (sourceA2746 + difference 3 1) (sourceB2746 + difference 1 3) sourceC2746) = raw37745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2746 sourceB2746 sourceC2746 difference raw37745; decide +kernel
    rw [ha]
    exact (canonical37745 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2746 + difference 3 2) (sourceB2746 + difference 2 3) sourceC2746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2746 + difference 3 2) (sourceB2746 + difference 2 3) sourceC2746) = raw37733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2746 sourceB2746 sourceC2746 difference raw37733; decide +kernel
    rw [ha]
    exact (canonical37733 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2746 + difference 3 3) (sourceB2746 + difference 3 3) sourceC2746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2746 + difference 3 3) (sourceB2746 + difference 3 3) sourceC2746) = raw37732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2746 sourceB2746 sourceC2746 difference raw37732; decide +kernel
    rw [ha]
    exact (canonical37732 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2746 + difference 3 4) (sourceB2746 + difference 4 3) sourceC2746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2746 + difference 3 4) (sourceB2746 + difference 4 3) sourceC2746) = raw37746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2746 sourceB2746 sourceC2746 difference raw37746; decide +kernel
    rw [ha]
    exact (canonical37746 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2746 + difference 3 5) (sourceB2746 + difference 5 3) sourceC2746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2181) := by
    have ha : (tripleCharges (sourceA2746 + difference 3 5) (sourceB2746 + difference 5 3) sourceC2746) = raw37737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2746 sourceB2746 sourceC2746 difference raw37737; decide +kernel
    rw [ha]
    exact (canonical37737 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2746 + sourceB2746) sourceC2746) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2746 + sourceB2746) sourceC2746) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2746 sourceB2746 sourceC2746 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2746 sourceB2746 sourceC2746
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2746, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2747 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceB2747 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2747 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2747 : Integer.Sparse Master := [(Sum.inr 2143, 1), (Sum.inr 2176, 1), (Sum.inr 2185, 1), (Sum.inr 2212, 2), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

theorem sourceEq2747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2747 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 0) (sourceB2747 + difference 0 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 0) (sourceB2747 + difference 0 2) sourceC2747) = raw37730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37730; decide +kernel
    rw [ha]
    exact (canonical37730 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 1) (sourceB2747 + difference 1 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 1) (sourceB2747 + difference 1 2) sourceC2747) = raw37743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37743; decide +kernel
    rw [ha]
    exact (canonical37743 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 2) (sourceB2747 + difference 2 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2176) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 2) (sourceB2747 + difference 2 2) sourceC2747) = raw37747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37747; decide +kernel
    rw [ha]
    exact (canonical37747 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 3) (sourceB2747 + difference 3 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 3) (sourceB2747 + difference 3 2) sourceC2747) = raw37748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37748; decide +kernel
    rw [ha]
    exact (canonical37748 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 4) (sourceB2747 + difference 4 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 4) (sourceB2747 + difference 4 2) sourceC2747) = raw37749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37749; decide +kernel
    rw [ha]
    exact (canonical37749 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 5) (sourceB2747 + difference 5 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 5) (sourceB2747 + difference 5 2) sourceC2747) = raw37726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37726; decide +kernel
    rw [ha]
    exact (canonical37726 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2747 + sourceB2747) sourceC2747) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2747 + sourceB2747) sourceC2747) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2747 sourceB2747 sourceC2747 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2747 sourceB2747 sourceC2747
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2747, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2748 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceB2748 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2748 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2748 : Integer.Sparse Master := [(Sum.inr 2165, 1), (Sum.inr 2186, 1), (Sum.inr 3420, 1), (Sum.inr 3457, 2), (Sum.inr 3510, 1), (Sum.inr 4074, -1)]

theorem sourceEq2748 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2748 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 0) (sourceB2748 + difference 0 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2165) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 0) (sourceB2748 + difference 0 2) sourceC2748) = raw37717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37717; decide +kernel
    rw [ha]
    exact (canonical37717 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 1) (sourceB2748 + difference 1 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 1) (sourceB2748 + difference 1 2) sourceC2748) = raw37733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37733; decide +kernel
    rw [ha]
    exact (canonical37733 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 2) (sourceB2748 + difference 2 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3510) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 2) (sourceB2748 + difference 2 2) sourceC2748) = raw37750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37750; decide +kernel
    rw [ha]
    exact (canonical37750 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 3) (sourceB2748 + difference 3 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 3) (sourceB2748 + difference 3 2) sourceC2748) = raw37714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37714; decide +kernel
    rw [ha]
    exact (canonical37714 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 4) (sourceB2748 + difference 4 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 4) (sourceB2748 + difference 4 2) sourceC2748) = raw37751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37751; decide +kernel
    rw [ha]
    exact (canonical37751 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 5) (sourceB2748 + difference 5 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 5) (sourceB2748 + difference 5 2) sourceC2748) = raw37721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37721; decide +kernel
    rw [ha]
    exact (canonical37721 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2748 + sourceB2748) sourceC2748) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2748 + sourceB2748) sourceC2748) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2748 sourceB2748 sourceC2748 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2748 sourceB2748 sourceC2748
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2748, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2749 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceB2749 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2749 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2749 : Integer.Sparse Master := [(Sum.inr 3323, 1), (Sum.inr 3327, 1), (Sum.inr 3329, 2), (Sum.inr 3420, 1), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

theorem sourceEq2749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2749 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2749 + difference 0 0) (sourceB2749 + difference 0 0) sourceC2749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2749 + difference 0 0) (sourceB2749 + difference 0 0) sourceC2749) = raw37726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2749 sourceB2749 sourceC2749 difference raw37726; decide +kernel
    rw [ha]
    exact (canonical37726 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2749 + difference 0 1) (sourceB2749 + difference 1 0) sourceC2749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2749 + difference 0 1) (sourceB2749 + difference 1 0) sourceC2749) = raw37740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2749 sourceB2749 sourceC2749 difference raw37740; decide +kernel
    rw [ha]
    exact (canonical37740 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2749 + difference 0 2) (sourceB2749 + difference 2 0) sourceC2749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3323) := by
    have ha : (tripleCharges (sourceA2749 + difference 0 2) (sourceB2749 + difference 2 0) sourceC2749) = raw37752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2749 sourceB2749 sourceC2749 difference raw37752; decide +kernel
    rw [ha]
    exact (canonical37752 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2749 + difference 0 3) (sourceB2749 + difference 3 0) sourceC2749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3329) := by
    have ha : (tripleCharges (sourceA2749 + difference 0 3) (sourceB2749 + difference 3 0) sourceC2749) = raw37753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2749 sourceB2749 sourceC2749 difference raw37753; decide +kernel
    rw [ha]
    exact (canonical37753 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2749 + difference 0 4) (sourceB2749 + difference 4 0) sourceC2749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3329) := by
    have ha : (tripleCharges (sourceA2749 + difference 0 4) (sourceB2749 + difference 4 0) sourceC2749) = raw37754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2749 sourceB2749 sourceC2749 difference raw37754; decide +kernel
    rw [ha]
    exact (canonical37754 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2749 + difference 0 5) (sourceB2749 + difference 5 0) sourceC2749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3327) := by
    have ha : (tripleCharges (sourceA2749 + difference 0 5) (sourceB2749 + difference 5 0) sourceC2749) = raw37755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2749 sourceB2749 sourceC2749 difference raw37755; decide +kernel
    rw [ha]
    exact (canonical37755 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2749 + sourceB2749) sourceC2749) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2749 + sourceB2749) sourceC2749) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2749 sourceB2749 sourceC2749 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2749 sourceB2749 sourceC2749
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2749, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2750 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceB2750 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2750 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2750 : Integer.Sparse Master := [(Sum.inr 2367, 1), (Sum.inr 3327, 1), (Sum.inr 3426, 1), (Sum.inr 3457, 2), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

theorem sourceEq2750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2750 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2750 + difference 0 5) (sourceB2750 + difference 5 0) sourceC2750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3327) := by
    have ha : (tripleCharges (sourceA2750 + difference 0 5) (sourceB2750 + difference 5 0) sourceC2750) = raw37755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2750 sourceB2750 sourceC2750 difference raw37755; decide +kernel
    rw [ha]
    exact (canonical37755 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2750 + difference 1 5) (sourceB2750 + difference 5 1) sourceC2750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2367) := by
    have ha : (tripleCharges (sourceA2750 + difference 1 5) (sourceB2750 + difference 5 1) sourceC2750) = raw37756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2750 sourceB2750 sourceC2750 difference raw37756; decide +kernel
    rw [ha]
    exact (canonical37756 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2750 + difference 2 5) (sourceB2750 + difference 5 2) sourceC2750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3426) := by
    have ha : (tripleCharges (sourceA2750 + difference 2 5) (sourceB2750 + difference 5 2) sourceC2750) = raw37757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2750 sourceB2750 sourceC2750 difference raw37757; decide +kernel
    rw [ha]
    exact (canonical37757 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2750 + difference 3 5) (sourceB2750 + difference 5 3) sourceC2750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2750 + difference 3 5) (sourceB2750 + difference 5 3) sourceC2750) = raw37751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2750 sourceB2750 sourceC2750 difference raw37751; decide +kernel
    rw [ha]
    exact (canonical37751 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2750 + difference 4 5) (sourceB2750 + difference 5 4) sourceC2750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2750 + difference 4 5) (sourceB2750 + difference 5 4) sourceC2750) = raw37714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2750 sourceB2750 sourceC2750 difference raw37714; decide +kernel
    rw [ha]
    exact (canonical37714 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2750 + difference 5 5) (sourceB2750 + difference 5 5) sourceC2750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2750 + difference 5 5) (sourceB2750 + difference 5 5) sourceC2750) = raw37726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2750 sourceB2750 sourceC2750 difference raw37726; decide +kernel
    rw [ha]
    exact (canonical37726 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2750 + sourceB2750) sourceC2750) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2750 + sourceB2750) sourceC2750) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2750 sourceB2750 sourceC2750 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2750 sourceB2750 sourceC2750
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2750, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2751 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceB2751 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2751 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2751 : Integer.Sparse Master := [(Sum.inr 1895, 1), (Sum.inr 3315, 1), (Sum.inr 3318, 1), (Sum.inr 3327, 1), (Sum.inr 3411, 1), (Sum.inr 3457, 1), (Sum.inr 4074, -1)]

theorem sourceEq2751 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2751 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2751 + difference 0 0) (sourceB2751 + difference 0 0) sourceC2751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2751 + difference 0 0) (sourceB2751 + difference 0 0) sourceC2751) = raw37714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2751 sourceB2751 sourceC2751 difference raw37714; decide +kernel
    rw [ha]
    exact (canonical37714 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2751 + difference 0 1) (sourceB2751 + difference 1 0) sourceC2751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2751 + difference 0 1) (sourceB2751 + difference 1 0) sourceC2751) = raw37731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2751 sourceB2751 sourceC2751 difference raw37731; decide +kernel
    rw [ha]
    exact (canonical37731 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2751 + difference 0 2) (sourceB2751 + difference 2 0) sourceC2751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3315) := by
    have ha : (tripleCharges (sourceA2751 + difference 0 2) (sourceB2751 + difference 2 0) sourceC2751) = raw37758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2751 sourceB2751 sourceC2751 difference raw37758; decide +kernel
    rw [ha]
    exact (canonical37758 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2751 + difference 0 3) (sourceB2751 + difference 3 0) sourceC2751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3318) := by
    have ha : (tripleCharges (sourceA2751 + difference 0 3) (sourceB2751 + difference 3 0) sourceC2751) = raw37759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2751 sourceB2751 sourceC2751 difference raw37759; decide +kernel
    rw [ha]
    exact (canonical37759 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2751 + difference 0 4) (sourceB2751 + difference 4 0) sourceC2751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3327) := by
    have ha : (tripleCharges (sourceA2751 + difference 0 4) (sourceB2751 + difference 4 0) sourceC2751) = raw37755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2751 sourceB2751 sourceC2751 difference raw37755; decide +kernel
    rw [ha]
    exact (canonical37755 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2751 + difference 0 5) (sourceB2751 + difference 5 0) sourceC2751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1895) := by
    have ha : (tripleCharges (sourceA2751 + difference 0 5) (sourceB2751 + difference 5 0) sourceC2751) = raw37760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2751 sourceB2751 sourceC2751 difference raw37760; decide +kernel
    rw [ha]
    exact (canonical37760 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2751 + sourceB2751) sourceC2751) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2751 + sourceB2751) sourceC2751) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2751 sourceB2751 sourceC2751 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2751 sourceB2751 sourceC2751
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2751, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
