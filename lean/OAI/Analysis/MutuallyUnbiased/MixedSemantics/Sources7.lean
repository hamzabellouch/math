import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical48

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA224 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB224 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC224 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm224 : Integer.Sparse Master := [(Sum.inr 1238, 2), (Sum.inr 1244, 1), (Sum.inr 1245, 1), (Sum.inr 1296, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

theorem sourceEq224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm224 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA224 + difference 0 0) (sourceB224 + difference 0 0) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA224 + difference 0 0) (sourceB224 + difference 0 0) sourceC224) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA224 + difference 1 0) (sourceB224 + difference 0 1) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1296) := by
    have ha : (tripleCharges (sourceA224 + difference 1 0) (sourceB224 + difference 0 1) sourceC224) = raw5868 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5868; decide +kernel
    rw [ha]
    exact (canonical5868 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA224 + difference 2 0) (sourceB224 + difference 0 2) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1238) := by
    have ha : (tripleCharges (sourceA224 + difference 2 0) (sourceB224 + difference 0 2) sourceC224) = raw5869 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5869; decide +kernel
    rw [ha]
    exact (canonical5869 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA224 + difference 3 0) (sourceB224 + difference 0 3) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1238) := by
    have ha : (tripleCharges (sourceA224 + difference 3 0) (sourceB224 + difference 0 3) sourceC224) = raw5870 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5870; decide +kernel
    rw [ha]
    exact (canonical5870 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA224 + difference 4 0) (sourceB224 + difference 0 4) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA224 + difference 4 0) (sourceB224 + difference 0 4) sourceC224) = raw5871 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5871; decide +kernel
    rw [ha]
    exact (canonical5871 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA224 + difference 5 0) (sourceB224 + difference 0 5) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1244) := by
    have ha : (tripleCharges (sourceA224 + difference 5 0) (sourceB224 + difference 0 5) sourceC224) = raw5872 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5872; decide +kernel
    rw [ha]
    exact (canonical5872 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA224 + sourceB224) sourceC224) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA224 + sourceB224) sourceC224) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA224 sourceB224 sourceC224 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA224 sourceB224 sourceC224
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm224, Integer.Sparse.eval]
  linarith only [hs]

def sourceA225 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB225 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC225 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm225 : Integer.Sparse Master := [(Sum.inr 1296, 1), (Sum.inr 2138, 1), (Sum.inr 2592, 2), (Sum.inr 2744, 1), (Sum.inr 2781, 1), (Sum.inr 4084, -1)]

theorem sourceEq225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm225 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA225 + difference 1 0) (sourceB225 + difference 0 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1296) := by
    have ha : (tripleCharges (sourceA225 + difference 1 0) (sourceB225 + difference 0 1) sourceC225) = raw5868 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5868; decide +kernel
    rw [ha]
    exact (canonical5868 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA225 + difference 1 1) (sourceB225 + difference 1 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA225 + difference 1 1) (sourceB225 + difference 1 1) sourceC225) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA225 + difference 1 2) (sourceB225 + difference 2 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2592) := by
    have ha : (tripleCharges (sourceA225 + difference 1 2) (sourceB225 + difference 2 1) sourceC225) = raw5873 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5873; decide +kernel
    rw [ha]
    exact (canonical5873 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA225 + difference 1 3) (sourceB225 + difference 3 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2592) := by
    have ha : (tripleCharges (sourceA225 + difference 1 3) (sourceB225 + difference 3 1) sourceC225) = raw5874 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5874; decide +kernel
    rw [ha]
    exact (canonical5874 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA225 + difference 1 4) (sourceB225 + difference 4 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA225 + difference 1 4) (sourceB225 + difference 4 1) sourceC225) = raw5875 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5875; decide +kernel
    rw [ha]
    exact (canonical5875 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA225 + difference 1 5) (sourceB225 + difference 5 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA225 + difference 1 5) (sourceB225 + difference 5 1) sourceC225) = raw5876 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5876; decide +kernel
    rw [ha]
    exact (canonical5876 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA225 + sourceB225) sourceC225) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA225 + sourceB225) sourceC225) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA225 sourceB225 sourceC225 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA225 sourceB225 sourceC225
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm225, Integer.Sparse.eval]
  linarith only [hs]

def sourceA226 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB226 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC226 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm226 : Integer.Sparse Master := [(Sum.inr 2513, 2), (Sum.inr 2520, 1), (Sum.inr 2522, 1), (Sum.inr 2744, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

theorem sourceEq226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm226 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA226 + difference 0 1) (sourceB226 + difference 1 0) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA226 + difference 0 1) (sourceB226 + difference 1 0) sourceC226) = raw5862 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5862; decide +kernel
    rw [ha]
    exact (canonical5862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA226 + difference 1 1) (sourceB226 + difference 1 1) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA226 + difference 1 1) (sourceB226 + difference 1 1) sourceC226) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA226 + difference 2 1) (sourceB226 + difference 1 2) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA226 + difference 2 1) (sourceB226 + difference 1 2) sourceC226) = raw5877 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5877; decide +kernel
    rw [ha]
    exact (canonical5877 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA226 + difference 3 1) (sourceB226 + difference 1 3) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA226 + difference 3 1) (sourceB226 + difference 1 3) sourceC226) = raw5878 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5878; decide +kernel
    rw [ha]
    exact (canonical5878 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA226 + difference 4 1) (sourceB226 + difference 1 4) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA226 + difference 4 1) (sourceB226 + difference 1 4) sourceC226) = raw5879 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5879; decide +kernel
    rw [ha]
    exact (canonical5879 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA226 + difference 5 1) (sourceB226 + difference 1 5) sourceC226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA226 + difference 5 1) (sourceB226 + difference 1 5) sourceC226) = raw5880 := by
      apply Matrix.ext; unfold tripleCharges sourceA226 sourceB226 sourceC226 difference raw5880; decide +kernel
    rw [ha]
    exact (canonical5880 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA226 + sourceB226) sourceC226) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA226 + sourceB226) sourceC226) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA226 sourceB226 sourceC226 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA226 sourceB226 sourceC226
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm226, Integer.Sparse.eval]
  linarith only [hs]

def sourceA227 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB227 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC227 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm227 : Integer.Sparse Master := [(Sum.inr 1238, 1), (Sum.inr 2133, 1), (Sum.inr 2513, 1), (Sum.inr 2555, 1), (Sum.inr 2738, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

theorem sourceEq227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm227 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA227 + difference 2 0) (sourceB227 + difference 0 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1238) := by
    have ha : (tripleCharges (sourceA227 + difference 2 0) (sourceB227 + difference 0 2) sourceC227) = raw5869 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5869; decide +kernel
    rw [ha]
    exact (canonical5869 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA227 + difference 2 1) (sourceB227 + difference 1 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA227 + difference 2 1) (sourceB227 + difference 1 2) sourceC227) = raw5877 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5877; decide +kernel
    rw [ha]
    exact (canonical5877 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA227 + difference 2 2) (sourceB227 + difference 2 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA227 + difference 2 2) (sourceB227 + difference 2 2) sourceC227) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA227 + difference 2 3) (sourceB227 + difference 3 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2555) := by
    have ha : (tripleCharges (sourceA227 + difference 2 3) (sourceB227 + difference 3 2) sourceC227) = raw5881 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5881; decide +kernel
    rw [ha]
    exact (canonical5881 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA227 + difference 2 4) (sourceB227 + difference 4 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA227 + difference 2 4) (sourceB227 + difference 4 2) sourceC227) = raw5882 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5882; decide +kernel
    rw [ha]
    exact (canonical5882 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA227 + difference 2 5) (sourceB227 + difference 5 2) sourceC227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA227 + difference 2 5) (sourceB227 + difference 5 2) sourceC227) = raw5883 := by
      apply Matrix.ext; unfold tripleCharges sourceA227 sourceB227 sourceC227 difference raw5883; decide +kernel
    rw [ha]
    exact (canonical5883 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA227 + sourceB227) sourceC227) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA227 + sourceB227) sourceC227) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA227 sourceB227 sourceC227 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA227 sourceB227 sourceC227
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm227, Integer.Sparse.eval]
  linarith only [hs]

def sourceA228 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB228 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC228 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm228 : Integer.Sparse Master := [(Sum.inr 2555, 1), (Sum.inr 2559, 1), (Sum.inr 2560, 1), (Sum.inr 2592, 1), (Sum.inr 2744, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem sourceEq228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm228 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA228 + difference 0 2) (sourceB228 + difference 2 0) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA228 + difference 0 2) (sourceB228 + difference 2 0) sourceC228) = raw5863 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5863; decide +kernel
    rw [ha]
    exact (canonical5863 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA228 + difference 1 2) (sourceB228 + difference 2 1) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2592) := by
    have ha : (tripleCharges (sourceA228 + difference 1 2) (sourceB228 + difference 2 1) sourceC228) = raw5873 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5873; decide +kernel
    rw [ha]
    exact (canonical5873 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA228 + difference 2 2) (sourceB228 + difference 2 2) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA228 + difference 2 2) (sourceB228 + difference 2 2) sourceC228) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA228 + difference 3 2) (sourceB228 + difference 2 3) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2555) := by
    have ha : (tripleCharges (sourceA228 + difference 3 2) (sourceB228 + difference 2 3) sourceC228) = raw5884 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5884; decide +kernel
    rw [ha]
    exact (canonical5884 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA228 + difference 4 2) (sourceB228 + difference 2 4) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA228 + difference 4 2) (sourceB228 + difference 2 4) sourceC228) = raw5885 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5885; decide +kernel
    rw [ha]
    exact (canonical5885 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA228 + difference 5 2) (sourceB228 + difference 2 5) sourceC228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2559) := by
    have ha : (tripleCharges (sourceA228 + difference 5 2) (sourceB228 + difference 2 5) sourceC228) = raw5886 := by
      apply Matrix.ext; unfold tripleCharges sourceA228 sourceB228 sourceC228 difference raw5886; decide +kernel
    rw [ha]
    exact (canonical5886 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA228 + sourceB228) sourceC228) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA228 + sourceB228) sourceC228) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA228 sourceB228 sourceC228 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA228 sourceB228 sourceC228
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm228, Integer.Sparse.eval]
  linarith only [hs]

def sourceA229 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB229 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC229 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm229 : Integer.Sparse Master := [(Sum.inr 1245, 1), (Sum.inr 2522, 1), (Sum.inr 2560, 2), (Sum.inr 2740, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

theorem sourceEq229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm229 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA229 + difference 4 0) (sourceB229 + difference 0 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA229 + difference 4 0) (sourceB229 + difference 0 4) sourceC229) = raw5871 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5871; decide +kernel
    rw [ha]
    exact (canonical5871 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA229 + difference 4 1) (sourceB229 + difference 1 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA229 + difference 4 1) (sourceB229 + difference 1 4) sourceC229) = raw5879 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5879; decide +kernel
    rw [ha]
    exact (canonical5879 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA229 + difference 4 2) (sourceB229 + difference 2 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA229 + difference 4 2) (sourceB229 + difference 2 4) sourceC229) = raw5885 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5885; decide +kernel
    rw [ha]
    exact (canonical5885 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA229 + difference 4 3) (sourceB229 + difference 3 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA229 + difference 4 3) (sourceB229 + difference 3 4) sourceC229) = raw5887 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5887; decide +kernel
    rw [ha]
    exact (canonical5887 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA229 + difference 4 4) (sourceB229 + difference 4 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA229 + difference 4 4) (sourceB229 + difference 4 4) sourceC229) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA229 + difference 4 5) (sourceB229 + difference 5 4) sourceC229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA229 + difference 4 5) (sourceB229 + difference 5 4) sourceC229) = raw5888 := by
      apply Matrix.ext; unfold tripleCharges sourceA229 sourceB229 sourceC229 difference raw5888; decide +kernel
    rw [ha]
    exact (canonical5888 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA229 + sourceB229) sourceC229) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA229 + sourceB229) sourceC229) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA229 sourceB229 sourceC229 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA229 sourceB229 sourceC229
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm229, Integer.Sparse.eval]
  linarith only [hs]

def sourceA230 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB230 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC230 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm230 : Integer.Sparse Master := [(Sum.inr 2133, 2), (Sum.inr 2136, 1), (Sum.inr 2138, 1), (Sum.inr 2279, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

theorem sourceEq230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm230 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA230 + difference 0 4) (sourceB230 + difference 4 0) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA230 + difference 0 4) (sourceB230 + difference 4 0) sourceC230) = raw5865 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5865; decide +kernel
    rw [ha]
    exact (canonical5865 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA230 + difference 1 4) (sourceB230 + difference 4 1) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA230 + difference 1 4) (sourceB230 + difference 4 1) sourceC230) = raw5875 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5875; decide +kernel
    rw [ha]
    exact (canonical5875 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA230 + difference 2 4) (sourceB230 + difference 4 2) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA230 + difference 2 4) (sourceB230 + difference 4 2) sourceC230) = raw5882 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5882; decide +kernel
    rw [ha]
    exact (canonical5882 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA230 + difference 3 4) (sourceB230 + difference 4 3) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA230 + difference 3 4) (sourceB230 + difference 4 3) sourceC230) = raw5889 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5889; decide +kernel
    rw [ha]
    exact (canonical5889 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA230 + difference 4 4) (sourceB230 + difference 4 4) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA230 + difference 4 4) (sourceB230 + difference 4 4) sourceC230) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA230 + difference 5 4) (sourceB230 + difference 4 5) sourceC230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA230 + difference 5 4) (sourceB230 + difference 4 5) sourceC230) = raw5890 := by
      apply Matrix.ext; unfold tripleCharges sourceA230 sourceB230 sourceC230 difference raw5890; decide +kernel
    rw [ha]
    exact (canonical5890 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA230 + sourceB230) sourceC230) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA230 + sourceB230) sourceC230) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA230 sourceB230 sourceC230 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA230 sourceB230 sourceC230
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm230, Integer.Sparse.eval]
  linarith only [hs]

def sourceA231 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB231 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC231 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm231 : Integer.Sparse Master := [(Sum.inr 1244, 1), (Sum.inr 2136, 1), (Sum.inr 2520, 1), (Sum.inr 2559, 2), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

theorem sourceEq231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm231 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA231 + difference 5 0) (sourceB231 + difference 0 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1244) := by
    have ha : (tripleCharges (sourceA231 + difference 5 0) (sourceB231 + difference 0 5) sourceC231) = raw5872 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5872; decide +kernel
    rw [ha]
    exact (canonical5872 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA231 + difference 5 1) (sourceB231 + difference 1 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA231 + difference 5 1) (sourceB231 + difference 1 5) sourceC231) = raw5880 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5880; decide +kernel
    rw [ha]
    exact (canonical5880 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA231 + difference 5 2) (sourceB231 + difference 2 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2559) := by
    have ha : (tripleCharges (sourceA231 + difference 5 2) (sourceB231 + difference 2 5) sourceC231) = raw5886 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5886; decide +kernel
    rw [ha]
    exact (canonical5886 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA231 + difference 5 3) (sourceB231 + difference 3 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2559) := by
    have ha : (tripleCharges (sourceA231 + difference 5 3) (sourceB231 + difference 3 5) sourceC231) = raw5891 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5891; decide +kernel
    rw [ha]
    exact (canonical5891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA231 + difference 5 4) (sourceB231 + difference 4 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA231 + difference 5 4) (sourceB231 + difference 4 5) sourceC231) = raw5890 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5890; decide +kernel
    rw [ha]
    exact (canonical5890 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA231 + difference 5 5) (sourceB231 + difference 5 5) sourceC231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA231 + difference 5 5) (sourceB231 + difference 5 5) sourceC231) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA231 sourceB231 sourceC231 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA231 + sourceB231) sourceC231) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA231 + sourceB231) sourceC231) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA231 sourceB231 sourceC231 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA231 sourceB231 sourceC231
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm231, Integer.Sparse.eval]
  linarith only [hs]

def sourceA232 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB232 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC232 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceForm232 : Integer.Sparse Master := [(Sum.inr 4425, 2), (Sum.inr 4429, 1), (Sum.inr 4430, 1), (Sum.inr 4500, 1), (Sum.inr 4567, 2), (Sum.inr 4574, 1), (Sum.inr 4617, 1), (Sum.inr 5019, 2), (Sum.inr 5022, 1), (Sum.inr 5060, 2), (Sum.inr 5062, 2), (Sum.inr 5103, 2), (Sum.inr 5173, 2), (Sum.inr 5267, 2), (Sum.inr 5268, 1), (Sum.inr 5295, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 1), (Sum.inr 5302, 1), (Sum.inr 5304, 1), (Sum.inr 5443, 1)]

theorem sourceEq232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm232 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA232 + difference 0 1) (sourceB232 + difference 1 0) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA232 + difference 0 1) (sourceB232 + difference 1 0) sourceC232) = raw5892 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5892; decide +kernel
    rw [ha]
    exact (canonical5892 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA232 + difference 0 2) (sourceB232 + difference 2 0) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA232 + difference 0 2) (sourceB232 + difference 2 0) sourceC232) = raw5893 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5893; decide +kernel
    rw [ha]
    exact (canonical5893 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA232 + difference 0 3) (sourceB232 + difference 3 0) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA232 + difference 0 3) (sourceB232 + difference 3 0) sourceC232) = raw5894 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5894; decide +kernel
    rw [ha]
    exact (canonical5894 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA232 + difference 0 4) (sourceB232 + difference 4 0) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA232 + difference 0 4) (sourceB232 + difference 4 0) sourceC232) = raw5895 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5895; decide +kernel
    rw [ha]
    exact (canonical5895 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA232 + difference 0 5) (sourceB232 + difference 5 0) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA232 + difference 0 5) (sourceB232 + difference 5 0) sourceC232) = raw5896 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5896; decide +kernel
    rw [ha]
    exact (canonical5896 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA232 + difference 1 0) (sourceB232 + difference 0 1) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA232 + difference 1 0) (sourceB232 + difference 0 1) sourceC232) = raw5897 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5897; decide +kernel
    rw [ha]
    exact (canonical5897 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA232 + difference 1 2) (sourceB232 + difference 2 1) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA232 + difference 1 2) (sourceB232 + difference 2 1) sourceC232) = raw5898 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5898; decide +kernel
    rw [ha]
    exact (canonical5898 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA232 + difference 1 3) (sourceB232 + difference 3 1) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA232 + difference 1 3) (sourceB232 + difference 3 1) sourceC232) = raw5899 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5899; decide +kernel
    rw [ha]
    exact (canonical5899 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA232 + difference 1 4) (sourceB232 + difference 4 1) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA232 + difference 1 4) (sourceB232 + difference 4 1) sourceC232) = raw5900 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5900; decide +kernel
    rw [ha]
    exact (canonical5900 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA232 + difference 1 5) (sourceB232 + difference 5 1) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA232 + difference 1 5) (sourceB232 + difference 5 1) sourceC232) = raw5901 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5901; decide +kernel
    rw [ha]
    exact (canonical5901 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA232 + difference 2 0) (sourceB232 + difference 0 2) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4425) := by
    have ha : (tripleCharges (sourceA232 + difference 2 0) (sourceB232 + difference 0 2) sourceC232) = raw5902 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5902; decide +kernel
    rw [ha]
    exact (canonical5902 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA232 + difference 2 1) (sourceB232 + difference 1 2) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5019) := by
    have ha : (tripleCharges (sourceA232 + difference 2 1) (sourceB232 + difference 1 2) sourceC232) = raw5903 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5903; decide +kernel
    rw [ha]
    exact (canonical5903 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA232 + difference 2 3) (sourceB232 + difference 3 2) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5060) := by
    have ha : (tripleCharges (sourceA232 + difference 2 3) (sourceB232 + difference 3 2) sourceC232) = raw5904 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5904; decide +kernel
    rw [ha]
    exact (canonical5904 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA232 + difference 2 4) (sourceB232 + difference 4 2) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA232 + difference 2 4) (sourceB232 + difference 4 2) sourceC232) = raw5905 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5905; decide +kernel
    rw [ha]
    exact (canonical5905 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA232 + difference 2 5) (sourceB232 + difference 5 2) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA232 + difference 2 5) (sourceB232 + difference 5 2) sourceC232) = raw5906 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5906; decide +kernel
    rw [ha]
    exact (canonical5906 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA232 + difference 3 0) (sourceB232 + difference 0 3) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4425) := by
    have ha : (tripleCharges (sourceA232 + difference 3 0) (sourceB232 + difference 0 3) sourceC232) = raw5907 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5907; decide +kernel
    rw [ha]
    exact (canonical5907 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA232 + difference 3 1) (sourceB232 + difference 1 3) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5019) := by
    have ha : (tripleCharges (sourceA232 + difference 3 1) (sourceB232 + difference 1 3) sourceC232) = raw5908 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5908; decide +kernel
    rw [ha]
    exact (canonical5908 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA232 + difference 3 2) (sourceB232 + difference 2 3) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5060) := by
    have ha : (tripleCharges (sourceA232 + difference 3 2) (sourceB232 + difference 2 3) sourceC232) = raw5909 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5909; decide +kernel
    rw [ha]
    exact (canonical5909 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA232 + difference 3 4) (sourceB232 + difference 4 3) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA232 + difference 3 4) (sourceB232 + difference 4 3) sourceC232) = raw5910 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5910; decide +kernel
    rw [ha]
    exact (canonical5910 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA232 + difference 3 5) (sourceB232 + difference 5 3) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA232 + difference 3 5) (sourceB232 + difference 5 3) sourceC232) = raw5911 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5911; decide +kernel
    rw [ha]
    exact (canonical5911 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA232 + difference 4 0) (sourceB232 + difference 0 4) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4430) := by
    have ha : (tripleCharges (sourceA232 + difference 4 0) (sourceB232 + difference 0 4) sourceC232) = raw5912 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5912; decide +kernel
    rw [ha]
    exact (canonical5912 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA232 + difference 4 1) (sourceB232 + difference 1 4) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4574) := by
    have ha : (tripleCharges (sourceA232 + difference 4 1) (sourceB232 + difference 1 4) sourceC232) = raw5913 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5913; decide +kernel
    rw [ha]
    exact (canonical5913 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA232 + difference 4 2) (sourceB232 + difference 2 4) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4567) := by
    have ha : (tripleCharges (sourceA232 + difference 4 2) (sourceB232 + difference 2 4) sourceC232) = raw5914 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5914; decide +kernel
    rw [ha]
    exact (canonical5914 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA232 + difference 4 3) (sourceB232 + difference 3 4) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4567) := by
    have ha : (tripleCharges (sourceA232 + difference 4 3) (sourceB232 + difference 3 4) sourceC232) = raw5915 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5915; decide +kernel
    rw [ha]
    exact (canonical5915 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA232 + difference 4 5) (sourceB232 + difference 5 4) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA232 + difference 4 5) (sourceB232 + difference 5 4) sourceC232) = raw5916 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5916; decide +kernel
    rw [ha]
    exact (canonical5916 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA232 + difference 5 0) (sourceB232 + difference 0 5) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4429) := by
    have ha : (tripleCharges (sourceA232 + difference 5 0) (sourceB232 + difference 0 5) sourceC232) = raw5917 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5917; decide +kernel
    rw [ha]
    exact (canonical5917 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA232 + difference 5 1) (sourceB232 + difference 1 5) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5022) := by
    have ha : (tripleCharges (sourceA232 + difference 5 1) (sourceB232 + difference 1 5) sourceC232) = raw5918 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5918; decide +kernel
    rw [ha]
    exact (canonical5918 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA232 + difference 5 2) (sourceB232 + difference 2 5) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5062) := by
    have ha : (tripleCharges (sourceA232 + difference 5 2) (sourceB232 + difference 2 5) sourceC232) = raw5919 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5919; decide +kernel
    rw [ha]
    exact (canonical5919 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA232 + difference 5 3) (sourceB232 + difference 3 5) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5062) := by
    have ha : (tripleCharges (sourceA232 + difference 5 3) (sourceB232 + difference 3 5) sourceC232) = raw5920 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5920; decide +kernel
    rw [ha]
    exact (canonical5920 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA232 + difference 5 4) (sourceB232 + difference 4 5) sourceC232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA232 + difference 5 4) (sourceB232 + difference 4 5) sourceC232) = raw5921 := by
      apply Matrix.ext; unfold tripleCharges sourceA232 sourceB232 sourceC232 difference raw5921; decide +kernel
    rw [ha]
    exact (canonical5921 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA232 sourceB232 sourceC232
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm232, Integer.Sparse.eval]
  linarith only [hs]

def sourceA233 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB233 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC233 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceForm233 : Integer.Sparse Master := [(Sum.inr 1006, 2), (Sum.inr 1010, 1), (Sum.inr 1011, 1), (Sum.inr 1084, 1), (Sum.inr 2405, 2), (Sum.inr 2408, 1), (Sum.inr 2409, 1), (Sum.inr 2463, 2), (Sum.inr 2465, 2), (Sum.inr 2466, 2), (Sum.inr 2513, 2), (Sum.inr 2732, 2), (Sum.inr 2734, 1), (Sum.inr 2735, 2), (Sum.inr 2737, 1), (Sum.inr 2776, 1), (Sum.inr 2781, 1), (Sum.inr 3573, 2), (Sum.inr 3583, 1), (Sum.inr 3584, 1), (Sum.inr 3889, 1)]

theorem sourceEq233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm233 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA233 + difference 0 1) (sourceB233 + difference 1 0) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA233 + difference 0 1) (sourceB233 + difference 1 0) sourceC233) = raw5922 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5922; decide +kernel
    rw [ha]
    exact (canonical5922 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA233 + difference 0 2) (sourceB233 + difference 2 0) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA233 + difference 0 2) (sourceB233 + difference 2 0) sourceC233) = raw5923 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5923; decide +kernel
    rw [ha]
    exact (canonical5923 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA233 + difference 0 3) (sourceB233 + difference 3 0) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA233 + difference 0 3) (sourceB233 + difference 3 0) sourceC233) = raw5924 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5924; decide +kernel
    rw [ha]
    exact (canonical5924 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA233 + difference 0 4) (sourceB233 + difference 4 0) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA233 + difference 0 4) (sourceB233 + difference 4 0) sourceC233) = raw5925 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5925; decide +kernel
    rw [ha]
    exact (canonical5925 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA233 + difference 0 5) (sourceB233 + difference 5 0) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA233 + difference 0 5) (sourceB233 + difference 5 0) sourceC233) = raw5926 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5926; decide +kernel
    rw [ha]
    exact (canonical5926 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA233 + difference 1 0) (sourceB233 + difference 0 1) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1084) := by
    have ha : (tripleCharges (sourceA233 + difference 1 0) (sourceB233 + difference 0 1) sourceC233) = raw5927 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5927; decide +kernel
    rw [ha]
    exact (canonical5927 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA233 + difference 1 2) (sourceB233 + difference 2 1) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA233 + difference 1 2) (sourceB233 + difference 2 1) sourceC233) = raw5928 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5928; decide +kernel
    rw [ha]
    exact (canonical5928 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA233 + difference 1 3) (sourceB233 + difference 3 1) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA233 + difference 1 3) (sourceB233 + difference 3 1) sourceC233) = raw5929 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5929; decide +kernel
    rw [ha]
    exact (canonical5929 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA233 + difference 1 4) (sourceB233 + difference 4 1) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA233 + difference 1 4) (sourceB233 + difference 4 1) sourceC233) = raw5930 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5930; decide +kernel
    rw [ha]
    exact (canonical5930 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA233 + difference 1 5) (sourceB233 + difference 5 1) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA233 + difference 1 5) (sourceB233 + difference 5 1) sourceC233) = raw5931 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5931; decide +kernel
    rw [ha]
    exact (canonical5931 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA233 + difference 2 0) (sourceB233 + difference 0 2) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1006) := by
    have ha : (tripleCharges (sourceA233 + difference 2 0) (sourceB233 + difference 0 2) sourceC233) = raw5932 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5932; decide +kernel
    rw [ha]
    exact (canonical5932 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA233 + difference 2 1) (sourceB233 + difference 1 2) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2405) := by
    have ha : (tripleCharges (sourceA233 + difference 2 1) (sourceB233 + difference 1 2) sourceC233) = raw5933 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5933; decide +kernel
    rw [ha]
    exact (canonical5933 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA233 + difference 2 3) (sourceB233 + difference 3 2) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2463) := by
    have ha : (tripleCharges (sourceA233 + difference 2 3) (sourceB233 + difference 3 2) sourceC233) = raw5934 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5934; decide +kernel
    rw [ha]
    exact (canonical5934 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA233 + difference 2 4) (sourceB233 + difference 4 2) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA233 + difference 2 4) (sourceB233 + difference 4 2) sourceC233) = raw5935 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5935; decide +kernel
    rw [ha]
    exact (canonical5935 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA233 + difference 2 5) (sourceB233 + difference 5 2) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA233 + difference 2 5) (sourceB233 + difference 5 2) sourceC233) = raw5936 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5936; decide +kernel
    rw [ha]
    exact (canonical5936 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA233 + difference 3 0) (sourceB233 + difference 0 3) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1006) := by
    have ha : (tripleCharges (sourceA233 + difference 3 0) (sourceB233 + difference 0 3) sourceC233) = raw5937 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5937; decide +kernel
    rw [ha]
    exact (canonical5937 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA233 + difference 3 1) (sourceB233 + difference 1 3) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2405) := by
    have ha : (tripleCharges (sourceA233 + difference 3 1) (sourceB233 + difference 1 3) sourceC233) = raw5938 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5938; decide +kernel
    rw [ha]
    exact (canonical5938 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA233 + difference 3 2) (sourceB233 + difference 2 3) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2463) := by
    have ha : (tripleCharges (sourceA233 + difference 3 2) (sourceB233 + difference 2 3) sourceC233) = raw5939 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5939; decide +kernel
    rw [ha]
    exact (canonical5939 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA233 + difference 3 4) (sourceB233 + difference 4 3) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA233 + difference 3 4) (sourceB233 + difference 4 3) sourceC233) = raw5940 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5940; decide +kernel
    rw [ha]
    exact (canonical5940 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA233 + difference 3 5) (sourceB233 + difference 5 3) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA233 + difference 3 5) (sourceB233 + difference 5 3) sourceC233) = raw5941 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5941; decide +kernel
    rw [ha]
    exact (canonical5941 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA233 + difference 4 0) (sourceB233 + difference 0 4) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1011) := by
    have ha : (tripleCharges (sourceA233 + difference 4 0) (sourceB233 + difference 0 4) sourceC233) = raw5942 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5942; decide +kernel
    rw [ha]
    exact (canonical5942 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA233 + difference 4 1) (sourceB233 + difference 1 4) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2409) := by
    have ha : (tripleCharges (sourceA233 + difference 4 1) (sourceB233 + difference 1 4) sourceC233) = raw5943 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5943; decide +kernel
    rw [ha]
    exact (canonical5943 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA233 + difference 4 2) (sourceB233 + difference 2 4) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2466) := by
    have ha : (tripleCharges (sourceA233 + difference 4 2) (sourceB233 + difference 2 4) sourceC233) = raw5944 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5944; decide +kernel
    rw [ha]
    exact (canonical5944 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA233 + difference 4 3) (sourceB233 + difference 3 4) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2466) := by
    have ha : (tripleCharges (sourceA233 + difference 4 3) (sourceB233 + difference 3 4) sourceC233) = raw5945 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5945; decide +kernel
    rw [ha]
    exact (canonical5945 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA233 + difference 4 5) (sourceB233 + difference 5 4) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA233 + difference 4 5) (sourceB233 + difference 5 4) sourceC233) = raw5946 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5946; decide +kernel
    rw [ha]
    exact (canonical5946 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA233 + difference 5 0) (sourceB233 + difference 0 5) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1010) := by
    have ha : (tripleCharges (sourceA233 + difference 5 0) (sourceB233 + difference 0 5) sourceC233) = raw5947 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5947; decide +kernel
    rw [ha]
    exact (canonical5947 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA233 + difference 5 1) (sourceB233 + difference 1 5) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2408) := by
    have ha : (tripleCharges (sourceA233 + difference 5 1) (sourceB233 + difference 1 5) sourceC233) = raw5948 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5948; decide +kernel
    rw [ha]
    exact (canonical5948 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA233 + difference 5 2) (sourceB233 + difference 2 5) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2465) := by
    have ha : (tripleCharges (sourceA233 + difference 5 2) (sourceB233 + difference 2 5) sourceC233) = raw5949 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5949; decide +kernel
    rw [ha]
    exact (canonical5949 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA233 + difference 5 3) (sourceB233 + difference 3 5) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2465) := by
    have ha : (tripleCharges (sourceA233 + difference 5 3) (sourceB233 + difference 3 5) sourceC233) = raw5950 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5950; decide +kernel
    rw [ha]
    exact (canonical5950 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA233 + difference 5 4) (sourceB233 + difference 4 5) sourceC233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA233 + difference 5 4) (sourceB233 + difference 4 5) sourceC233) = raw5951 := by
      apply Matrix.ext; unfold tripleCharges sourceA233 sourceB233 sourceC233 difference raw5951; decide +kernel
    rw [ha]
    exact (canonical5951 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA233 sourceB233 sourceC233
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm233, Integer.Sparse.eval]
  linarith only [hs]

def sourceA234 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB234 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC234 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceForm234 : Integer.Sparse Master := [(Sum.inr 1184, 2), (Sum.inr 1186, 1), (Sum.inr 1192, 1), (Sum.inr 1292, 1), (Sum.inr 1610, 2), (Sum.inr 1628, 1), (Sum.inr 1716, 1), (Sum.inr 2837, 2), (Sum.inr 2842, 1), (Sum.inr 2906, 2), (Sum.inr 2910, 2), (Sum.inr 2952, 2), (Sum.inr 3024, 2), (Sum.inr 3051, 2), (Sum.inr 3055, 1), (Sum.inr 3098, 1), (Sum.inr 3119, 1), (Sum.inr 3541, 2), (Sum.inr 3549, 1), (Sum.inr 3626, 1), (Sum.inr 3862, 1)]

theorem sourceEq234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm234 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA234 + difference 0 1) (sourceB234 + difference 1 0) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA234 + difference 0 1) (sourceB234 + difference 1 0) sourceC234) = raw5952 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5952; decide +kernel
    rw [ha]
    exact (canonical5952 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA234 + difference 0 2) (sourceB234 + difference 2 0) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA234 + difference 0 2) (sourceB234 + difference 2 0) sourceC234) = raw5953 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5953; decide +kernel
    rw [ha]
    exact (canonical5953 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA234 + difference 0 3) (sourceB234 + difference 3 0) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA234 + difference 0 3) (sourceB234 + difference 3 0) sourceC234) = raw5954 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5954; decide +kernel
    rw [ha]
    exact (canonical5954 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA234 + difference 0 4) (sourceB234 + difference 4 0) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA234 + difference 0 4) (sourceB234 + difference 4 0) sourceC234) = raw5955 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5955; decide +kernel
    rw [ha]
    exact (canonical5955 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA234 + difference 0 5) (sourceB234 + difference 5 0) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA234 + difference 0 5) (sourceB234 + difference 5 0) sourceC234) = raw5956 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5956; decide +kernel
    rw [ha]
    exact (canonical5956 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA234 + difference 1 0) (sourceB234 + difference 0 1) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA234 + difference 1 0) (sourceB234 + difference 0 1) sourceC234) = raw5957 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5957; decide +kernel
    rw [ha]
    exact (canonical5957 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA234 + difference 1 2) (sourceB234 + difference 2 1) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA234 + difference 1 2) (sourceB234 + difference 2 1) sourceC234) = raw5958 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5958; decide +kernel
    rw [ha]
    exact (canonical5958 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA234 + difference 1 3) (sourceB234 + difference 3 1) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA234 + difference 1 3) (sourceB234 + difference 3 1) sourceC234) = raw5959 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5959; decide +kernel
    rw [ha]
    exact (canonical5959 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA234 + difference 1 4) (sourceB234 + difference 4 1) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA234 + difference 1 4) (sourceB234 + difference 4 1) sourceC234) = raw5960 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5960; decide +kernel
    rw [ha]
    exact (canonical5960 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA234 + difference 1 5) (sourceB234 + difference 5 1) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA234 + difference 1 5) (sourceB234 + difference 5 1) sourceC234) = raw5961 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5961; decide +kernel
    rw [ha]
    exact (canonical5961 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA234 + difference 2 0) (sourceB234 + difference 0 2) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1610) := by
    have ha : (tripleCharges (sourceA234 + difference 2 0) (sourceB234 + difference 0 2) sourceC234) = raw5962 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5962; decide +kernel
    rw [ha]
    exact (canonical5962 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA234 + difference 2 1) (sourceB234 + difference 1 2) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2910) := by
    have ha : (tripleCharges (sourceA234 + difference 2 1) (sourceB234 + difference 1 2) sourceC234) = raw5963 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5963; decide +kernel
    rw [ha]
    exact (canonical5963 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA234 + difference 2 3) (sourceB234 + difference 3 2) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2906) := by
    have ha : (tripleCharges (sourceA234 + difference 2 3) (sourceB234 + difference 3 2) sourceC234) = raw5964 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5964; decide +kernel
    rw [ha]
    exact (canonical5964 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA234 + difference 2 4) (sourceB234 + difference 4 2) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA234 + difference 2 4) (sourceB234 + difference 4 2) sourceC234) = raw5965 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5965; decide +kernel
    rw [ha]
    exact (canonical5965 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA234 + difference 2 5) (sourceB234 + difference 5 2) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA234 + difference 2 5) (sourceB234 + difference 5 2) sourceC234) = raw5966 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5966; decide +kernel
    rw [ha]
    exact (canonical5966 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA234 + difference 3 0) (sourceB234 + difference 0 3) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1610) := by
    have ha : (tripleCharges (sourceA234 + difference 3 0) (sourceB234 + difference 0 3) sourceC234) = raw5967 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5967; decide +kernel
    rw [ha]
    exact (canonical5967 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA234 + difference 3 1) (sourceB234 + difference 1 3) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2910) := by
    have ha : (tripleCharges (sourceA234 + difference 3 1) (sourceB234 + difference 1 3) sourceC234) = raw5968 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5968; decide +kernel
    rw [ha]
    exact (canonical5968 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA234 + difference 3 2) (sourceB234 + difference 2 3) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2906) := by
    have ha : (tripleCharges (sourceA234 + difference 3 2) (sourceB234 + difference 2 3) sourceC234) = raw5969 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5969; decide +kernel
    rw [ha]
    exact (canonical5969 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA234 + difference 3 4) (sourceB234 + difference 4 3) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA234 + difference 3 4) (sourceB234 + difference 4 3) sourceC234) = raw5970 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5970; decide +kernel
    rw [ha]
    exact (canonical5970 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA234 + difference 3 5) (sourceB234 + difference 5 3) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA234 + difference 3 5) (sourceB234 + difference 5 3) sourceC234) = raw5971 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5971; decide +kernel
    rw [ha]
    exact (canonical5971 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA234 + difference 4 0) (sourceB234 + difference 0 4) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1186) := by
    have ha : (tripleCharges (sourceA234 + difference 4 0) (sourceB234 + difference 0 4) sourceC234) = raw5972 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5972; decide +kernel
    rw [ha]
    exact (canonical5972 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA234 + difference 4 1) (sourceB234 + difference 1 4) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1192) := by
    have ha : (tripleCharges (sourceA234 + difference 4 1) (sourceB234 + difference 1 4) sourceC234) = raw5973 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5973; decide +kernel
    rw [ha]
    exact (canonical5973 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA234 + difference 4 2) (sourceB234 + difference 2 4) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1184) := by
    have ha : (tripleCharges (sourceA234 + difference 4 2) (sourceB234 + difference 2 4) sourceC234) = raw5974 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5974; decide +kernel
    rw [ha]
    exact (canonical5974 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA234 + difference 4 3) (sourceB234 + difference 3 4) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1184) := by
    have ha : (tripleCharges (sourceA234 + difference 4 3) (sourceB234 + difference 3 4) sourceC234) = raw5975 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5975; decide +kernel
    rw [ha]
    exact (canonical5975 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA234 + difference 4 5) (sourceB234 + difference 5 4) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1292) := by
    have ha : (tripleCharges (sourceA234 + difference 4 5) (sourceB234 + difference 5 4) sourceC234) = raw5976 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5976; decide +kernel
    rw [ha]
    exact (canonical5976 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA234 + difference 5 0) (sourceB234 + difference 0 5) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1628) := by
    have ha : (tripleCharges (sourceA234 + difference 5 0) (sourceB234 + difference 0 5) sourceC234) = raw5977 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5977; decide +kernel
    rw [ha]
    exact (canonical5977 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA234 + difference 5 1) (sourceB234 + difference 1 5) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2842) := by
    have ha : (tripleCharges (sourceA234 + difference 5 1) (sourceB234 + difference 1 5) sourceC234) = raw5978 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5978; decide +kernel
    rw [ha]
    exact (canonical5978 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA234 + difference 5 2) (sourceB234 + difference 2 5) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA234 + difference 5 2) (sourceB234 + difference 2 5) sourceC234) = raw5979 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5979; decide +kernel
    rw [ha]
    exact (canonical5979 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA234 + difference 5 3) (sourceB234 + difference 3 5) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA234 + difference 5 3) (sourceB234 + difference 3 5) sourceC234) = raw5980 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5980; decide +kernel
    rw [ha]
    exact (canonical5980 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA234 + difference 5 4) (sourceB234 + difference 4 5) sourceC234) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA234 + difference 5 4) (sourceB234 + difference 4 5) sourceC234) = raw5981 := by
      apply Matrix.ext; unfold tripleCharges sourceA234 sourceB234 sourceC234 difference raw5981; decide +kernel
    rw [ha]
    exact (canonical5981 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA234 sourceB234 sourceC234
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm234, Integer.Sparse.eval]
  linarith only [hs]

def sourceA235 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB235 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC235 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceForm235 : Integer.Sparse Master := [(Sum.inr 2773, 2), (Sum.inr 2774, 1), (Sum.inr 2777, 1), (Sum.inr 2782, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

theorem sourceEq235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm235 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA235 + difference 0 0) (sourceB235 + difference 0 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA235 + difference 0 0) (sourceB235 + difference 0 0) sourceC235) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA235 + difference 0 1) (sourceB235 + difference 1 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA235 + difference 0 1) (sourceB235 + difference 1 0) sourceC235) = raw5983 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5983; decide +kernel
    rw [ha]
    exact (canonical5983 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA235 + difference 0 2) (sourceB235 + difference 2 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA235 + difference 0 2) (sourceB235 + difference 2 0) sourceC235) = raw5984 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5984; decide +kernel
    rw [ha]
    exact (canonical5984 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA235 + difference 0 3) (sourceB235 + difference 3 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA235 + difference 0 3) (sourceB235 + difference 3 0) sourceC235) = raw5985 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5985; decide +kernel
    rw [ha]
    exact (canonical5985 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA235 + difference 0 4) (sourceB235 + difference 4 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA235 + difference 0 4) (sourceB235 + difference 4 0) sourceC235) = raw5986 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5986; decide +kernel
    rw [ha]
    exact (canonical5986 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA235 + difference 0 5) (sourceB235 + difference 5 0) sourceC235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA235 + difference 0 5) (sourceB235 + difference 5 0) sourceC235) = raw5987 := by
      apply Matrix.ext; unfold tripleCharges sourceA235 sourceB235 sourceC235 difference raw5987; decide +kernel
    rw [ha]
    exact (canonical5987 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA235 + sourceB235) sourceC235) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA235 + sourceB235) sourceC235) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA235 sourceB235 sourceC235 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA235 sourceB235 sourceC235
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm235, Integer.Sparse.eval]
  linarith only [hs]

def sourceA236 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB236 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC236 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceForm236 : Integer.Sparse Master := [(Sum.inr 1282, 1), (Sum.inr 1422, 2), (Sum.inr 1424, 1), (Sum.inr 1436, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

theorem sourceEq236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm236 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA236 + difference 0 0) (sourceB236 + difference 0 0) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA236 + difference 0 0) (sourceB236 + difference 0 0) sourceC236) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA236 + difference 1 0) (sourceB236 + difference 0 1) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA236 + difference 1 0) (sourceB236 + difference 0 1) sourceC236) = raw5989 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5989; decide +kernel
    rw [ha]
    exact (canonical5989 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA236 + difference 2 0) (sourceB236 + difference 0 2) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1422) := by
    have ha : (tripleCharges (sourceA236 + difference 2 0) (sourceB236 + difference 0 2) sourceC236) = raw5990 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5990; decide +kernel
    rw [ha]
    exact (canonical5990 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA236 + difference 3 0) (sourceB236 + difference 0 3) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1422) := by
    have ha : (tripleCharges (sourceA236 + difference 3 0) (sourceB236 + difference 0 3) sourceC236) = raw5991 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5991; decide +kernel
    rw [ha]
    exact (canonical5991 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA236 + difference 4 0) (sourceB236 + difference 0 4) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1282) := by
    have ha : (tripleCharges (sourceA236 + difference 4 0) (sourceB236 + difference 0 4) sourceC236) = raw5992 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5992; decide +kernel
    rw [ha]
    exact (canonical5992 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA236 + difference 5 0) (sourceB236 + difference 0 5) sourceC236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1424) := by
    have ha : (tripleCharges (sourceA236 + difference 5 0) (sourceB236 + difference 0 5) sourceC236) = raw5993 := by
      apply Matrix.ext; unfold tripleCharges sourceA236 sourceB236 sourceC236 difference raw5993; decide +kernel
    rw [ha]
    exact (canonical5993 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA236 + sourceB236) sourceC236) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA236 + sourceB236) sourceC236) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA236 sourceB236 sourceC236 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA236 sourceB236 sourceC236
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm236, Integer.Sparse.eval]
  linarith only [hs]

def sourceA237 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB237 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC237 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceForm237 : Integer.Sparse Master := [(Sum.inr 1436, 1), (Sum.inr 2759, 2), (Sum.inr 2769, 1), (Sum.inr 2777, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

theorem sourceEq237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm237 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA237 + difference 1 0) (sourceB237 + difference 0 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA237 + difference 1 0) (sourceB237 + difference 0 1) sourceC237) = raw5989 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5989; decide +kernel
    rw [ha]
    exact (canonical5989 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA237 + difference 1 1) (sourceB237 + difference 1 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA237 + difference 1 1) (sourceB237 + difference 1 1) sourceC237) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA237 + difference 1 2) (sourceB237 + difference 2 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA237 + difference 1 2) (sourceB237 + difference 2 1) sourceC237) = raw5994 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5994; decide +kernel
    rw [ha]
    exact (canonical5994 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA237 + difference 1 3) (sourceB237 + difference 3 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA237 + difference 1 3) (sourceB237 + difference 3 1) sourceC237) = raw5995 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5995; decide +kernel
    rw [ha]
    exact (canonical5995 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA237 + difference 1 4) (sourceB237 + difference 4 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA237 + difference 1 4) (sourceB237 + difference 4 1) sourceC237) = raw5996 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5996; decide +kernel
    rw [ha]
    exact (canonical5996 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA237 + difference 1 5) (sourceB237 + difference 5 1) sourceC237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA237 + difference 1 5) (sourceB237 + difference 5 1) sourceC237) = raw5997 := by
      apply Matrix.ext; unfold tripleCharges sourceA237 sourceB237 sourceC237 difference raw5997; decide +kernel
    rw [ha]
    exact (canonical5997 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA237 + sourceB237) sourceC237) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA237 + sourceB237) sourceC237) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA237 sourceB237 sourceC237 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA237 sourceB237 sourceC237
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm237, Integer.Sparse.eval]
  linarith only [hs]

def sourceA238 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB238 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC238 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceForm238 : Integer.Sparse Master := [(Sum.inr 1283, 1), (Sum.inr 2582, 2), (Sum.inr 2651, 1), (Sum.inr 2774, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

theorem sourceEq238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm238 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA238 + difference 0 1) (sourceB238 + difference 1 0) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA238 + difference 0 1) (sourceB238 + difference 1 0) sourceC238) = raw5983 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw5983; decide +kernel
    rw [ha]
    exact (canonical5983 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA238 + difference 1 1) (sourceB238 + difference 1 1) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA238 + difference 1 1) (sourceB238 + difference 1 1) sourceC238) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA238 + difference 2 1) (sourceB238 + difference 1 2) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2582) := by
    have ha : (tripleCharges (sourceA238 + difference 2 1) (sourceB238 + difference 1 2) sourceC238) = raw5998 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw5998; decide +kernel
    rw [ha]
    exact (canonical5998 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA238 + difference 3 1) (sourceB238 + difference 1 3) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2582) := by
    have ha : (tripleCharges (sourceA238 + difference 3 1) (sourceB238 + difference 1 3) sourceC238) = raw5999 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw5999; decide +kernel
    rw [ha]
    exact (canonical5999 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA238 + difference 4 1) (sourceB238 + difference 1 4) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1283) := by
    have ha : (tripleCharges (sourceA238 + difference 4 1) (sourceB238 + difference 1 4) sourceC238) = raw6000 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw6000; decide +kernel
    rw [ha]
    exact (canonical6000 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA238 + difference 5 1) (sourceB238 + difference 1 5) sourceC238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2651) := by
    have ha : (tripleCharges (sourceA238 + difference 5 1) (sourceB238 + difference 1 5) sourceC238) = raw6001 := by
      apply Matrix.ext; unfold tripleCharges sourceA238 sourceB238 sourceC238 difference raw6001; decide +kernel
    rw [ha]
    exact (canonical6001 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA238 + sourceB238) sourceC238) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA238 + sourceB238) sourceC238) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA238 sourceB238 sourceC238 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA238 sourceB238 sourceC238
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm238, Integer.Sparse.eval]
  linarith only [hs]

def sourceA239 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB239 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC239 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceForm239 : Integer.Sparse Master := [(Sum.inr 1422, 1), (Sum.inr 2580, 1), (Sum.inr 2582, 1), (Sum.inr 2600, 1), (Sum.inr 2777, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

theorem sourceEq239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm239 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA239 + difference 2 0) (sourceB239 + difference 0 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1422) := by
    have ha : (tripleCharges (sourceA239 + difference 2 0) (sourceB239 + difference 0 2) sourceC239) = raw5990 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw5990; decide +kernel
    rw [ha]
    exact (canonical5990 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA239 + difference 2 1) (sourceB239 + difference 1 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2582) := by
    have ha : (tripleCharges (sourceA239 + difference 2 1) (sourceB239 + difference 1 2) sourceC239) = raw5998 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw5998; decide +kernel
    rw [ha]
    exact (canonical5998 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA239 + difference 2 2) (sourceB239 + difference 2 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA239 + difference 2 2) (sourceB239 + difference 2 2) sourceC239) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA239 + difference 2 3) (sourceB239 + difference 3 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2580) := by
    have ha : (tripleCharges (sourceA239 + difference 2 3) (sourceB239 + difference 3 2) sourceC239) = raw6002 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw6002; decide +kernel
    rw [ha]
    exact (canonical6002 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA239 + difference 2 4) (sourceB239 + difference 4 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA239 + difference 2 4) (sourceB239 + difference 4 2) sourceC239) = raw6003 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw6003; decide +kernel
    rw [ha]
    exact (canonical6003 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA239 + difference 2 5) (sourceB239 + difference 5 2) sourceC239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA239 + difference 2 5) (sourceB239 + difference 5 2) sourceC239) = raw6004 := by
      apply Matrix.ext; unfold tripleCharges sourceA239 sourceB239 sourceC239 difference raw6004; decide +kernel
    rw [ha]
    exact (canonical6004 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA239 + sourceB239) sourceC239) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA239 + sourceB239) sourceC239) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA239 sourceB239 sourceC239 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA239 sourceB239 sourceC239
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm239, Integer.Sparse.eval]
  linarith only [hs]

def sourceA240 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB240 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC240 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceForm240 : Integer.Sparse Master := [(Sum.inr 1280, 1), (Sum.inr 2580, 1), (Sum.inr 2647, 1), (Sum.inr 2759, 1), (Sum.inr 2773, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

theorem sourceEq240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm240 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA240 + difference 0 2) (sourceB240 + difference 2 0) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA240 + difference 0 2) (sourceB240 + difference 2 0) sourceC240) = raw5984 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw5984; decide +kernel
    rw [ha]
    exact (canonical5984 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA240 + difference 1 2) (sourceB240 + difference 2 1) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA240 + difference 1 2) (sourceB240 + difference 2 1) sourceC240) = raw5994 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw5994; decide +kernel
    rw [ha]
    exact (canonical5994 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA240 + difference 2 2) (sourceB240 + difference 2 2) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA240 + difference 2 2) (sourceB240 + difference 2 2) sourceC240) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA240 + difference 3 2) (sourceB240 + difference 2 3) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2580) := by
    have ha : (tripleCharges (sourceA240 + difference 3 2) (sourceB240 + difference 2 3) sourceC240) = raw6005 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw6005; decide +kernel
    rw [ha]
    exact (canonical6005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA240 + difference 4 2) (sourceB240 + difference 2 4) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1280) := by
    have ha : (tripleCharges (sourceA240 + difference 4 2) (sourceB240 + difference 2 4) sourceC240) = raw6006 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw6006; decide +kernel
    rw [ha]
    exact (canonical6006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA240 + difference 5 2) (sourceB240 + difference 2 5) sourceC240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2647) := by
    have ha : (tripleCharges (sourceA240 + difference 5 2) (sourceB240 + difference 2 5) sourceC240) = raw6007 := by
      apply Matrix.ext; unfold tripleCharges sourceA240 sourceB240 sourceC240 difference raw6007; decide +kernel
    rw [ha]
    exact (canonical6007 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA240 + sourceB240) sourceC240) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA240 + sourceB240) sourceC240) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA240 sourceB240 sourceC240 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA240 sourceB240 sourceC240
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm240, Integer.Sparse.eval]
  linarith only [hs]

def sourceA241 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB241 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC241 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceForm241 : Integer.Sparse Master := [(Sum.inr 1280, 2), (Sum.inr 1282, 1), (Sum.inr 1283, 1), (Sum.inr 1306, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

theorem sourceEq241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm241 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA241 + difference 4 0) (sourceB241 + difference 0 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1282) := by
    have ha : (tripleCharges (sourceA241 + difference 4 0) (sourceB241 + difference 0 4) sourceC241) = raw5992 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw5992; decide +kernel
    rw [ha]
    exact (canonical5992 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA241 + difference 4 1) (sourceB241 + difference 1 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1283) := by
    have ha : (tripleCharges (sourceA241 + difference 4 1) (sourceB241 + difference 1 4) sourceC241) = raw6000 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw6000; decide +kernel
    rw [ha]
    exact (canonical6000 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA241 + difference 4 2) (sourceB241 + difference 2 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1280) := by
    have ha : (tripleCharges (sourceA241 + difference 4 2) (sourceB241 + difference 2 4) sourceC241) = raw6006 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw6006; decide +kernel
    rw [ha]
    exact (canonical6006 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA241 + difference 4 3) (sourceB241 + difference 3 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1280) := by
    have ha : (tripleCharges (sourceA241 + difference 4 3) (sourceB241 + difference 3 4) sourceC241) = raw6008 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw6008; decide +kernel
    rw [ha]
    exact (canonical6008 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA241 + difference 4 4) (sourceB241 + difference 4 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA241 + difference 4 4) (sourceB241 + difference 4 4) sourceC241) = raw5982 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw5982; decide +kernel
    rw [ha]
    exact (canonical5982 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA241 + difference 4 5) (sourceB241 + difference 5 4) sourceC241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA241 + difference 4 5) (sourceB241 + difference 5 4) sourceC241) = raw6009 := by
      apply Matrix.ext; unfold tripleCharges sourceA241 sourceB241 sourceC241 difference raw6009; decide +kernel
    rw [ha]
    exact (canonical6009 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA241 + sourceB241) sourceC241) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA241 + sourceB241) sourceC241) = raw5988 := by
      apply Matrix.ext; unfold doubleCharges sourceA241 sourceB241 sourceC241 raw5988; decide +kernel
    rw [ha]
    exact (canonical5988 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA241 sourceB241 sourceC241
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm241, Integer.Sparse.eval]
  linarith only [hs]

def sourceA242 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB242 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC242 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm242 : Integer.Sparse Master := [(Sum.inr 4477, 2), (Sum.inr 4478, 1), (Sum.inr 4479, 1), (Sum.inr 4504, 1), (Sum.inr 4817, 2), (Sum.inr 4843, 1), (Sum.inr 4899, 1), (Sum.inr 5088, 2), (Sum.inr 5089, 2), (Sum.inr 5106, 2), (Sum.inr 5175, 1), (Sum.inr 5205, 2), (Sum.inr 5206, 1), (Sum.inr 5260, 2), (Sum.inr 5275, 1), (Sum.inr 5276, 2), (Sum.inr 5279, 2), (Sum.inr 5291, 1), (Sum.inr 5297, 1), (Sum.inr 5310, 1), (Sum.inr 5311, 1)]

theorem sourceEq242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm242 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA242 + difference 0 1) (sourceB242 + difference 1 0) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5297) := by
    have ha : (tripleCharges (sourceA242 + difference 0 1) (sourceB242 + difference 1 0) sourceC242) = raw6010 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6010; decide +kernel
    rw [ha]
    exact (canonical6010 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA242 + difference 0 2) (sourceB242 + difference 2 0) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA242 + difference 0 2) (sourceB242 + difference 2 0) sourceC242) = raw6011 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6011; decide +kernel
    rw [ha]
    exact (canonical6011 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA242 + difference 0 3) (sourceB242 + difference 3 0) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA242 + difference 0 3) (sourceB242 + difference 3 0) sourceC242) = raw6012 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6012; decide +kernel
    rw [ha]
    exact (canonical6012 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA242 + difference 0 4) (sourceB242 + difference 4 0) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA242 + difference 0 4) (sourceB242 + difference 4 0) sourceC242) = raw6013 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6013; decide +kernel
    rw [ha]
    exact (canonical6013 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA242 + difference 0 5) (sourceB242 + difference 5 0) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA242 + difference 0 5) (sourceB242 + difference 5 0) sourceC242) = raw6014 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6014; decide +kernel
    rw [ha]
    exact (canonical6014 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA242 + difference 1 0) (sourceB242 + difference 0 1) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA242 + difference 1 0) (sourceB242 + difference 0 1) sourceC242) = raw6015 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6015; decide +kernel
    rw [ha]
    exact (canonical6015 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA242 + difference 1 2) (sourceB242 + difference 2 1) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA242 + difference 1 2) (sourceB242 + difference 2 1) sourceC242) = raw6016 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6016; decide +kernel
    rw [ha]
    exact (canonical6016 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA242 + difference 1 3) (sourceB242 + difference 3 1) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA242 + difference 1 3) (sourceB242 + difference 3 1) sourceC242) = raw6017 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6017; decide +kernel
    rw [ha]
    exact (canonical6017 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA242 + difference 1 4) (sourceB242 + difference 4 1) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA242 + difference 1 4) (sourceB242 + difference 4 1) sourceC242) = raw6018 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6018; decide +kernel
    rw [ha]
    exact (canonical6018 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA242 + difference 1 5) (sourceB242 + difference 5 1) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5311) := by
    have ha : (tripleCharges (sourceA242 + difference 1 5) (sourceB242 + difference 5 1) sourceC242) = raw6019 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6019; decide +kernel
    rw [ha]
    exact (canonical6019 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA242 + difference 2 0) (sourceB242 + difference 0 2) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA242 + difference 2 0) (sourceB242 + difference 0 2) sourceC242) = raw6020 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6020; decide +kernel
    rw [ha]
    exact (canonical6020 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA242 + difference 2 1) (sourceB242 + difference 1 2) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5089) := by
    have ha : (tripleCharges (sourceA242 + difference 2 1) (sourceB242 + difference 1 2) sourceC242) = raw6021 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6021; decide +kernel
    rw [ha]
    exact (canonical6021 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA242 + difference 2 3) (sourceB242 + difference 3 2) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5088) := by
    have ha : (tripleCharges (sourceA242 + difference 2 3) (sourceB242 + difference 3 2) sourceC242) = raw6022 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6022; decide +kernel
    rw [ha]
    exact (canonical6022 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA242 + difference 2 4) (sourceB242 + difference 4 2) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA242 + difference 2 4) (sourceB242 + difference 4 2) sourceC242) = raw6023 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6023; decide +kernel
    rw [ha]
    exact (canonical6023 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA242 + difference 2 5) (sourceB242 + difference 5 2) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5106) := by
    have ha : (tripleCharges (sourceA242 + difference 2 5) (sourceB242 + difference 5 2) sourceC242) = raw6024 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6024; decide +kernel
    rw [ha]
    exact (canonical6024 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA242 + difference 3 0) (sourceB242 + difference 0 3) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA242 + difference 3 0) (sourceB242 + difference 0 3) sourceC242) = raw6025 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6025; decide +kernel
    rw [ha]
    exact (canonical6025 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA242 + difference 3 1) (sourceB242 + difference 1 3) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5089) := by
    have ha : (tripleCharges (sourceA242 + difference 3 1) (sourceB242 + difference 1 3) sourceC242) = raw6026 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6026; decide +kernel
    rw [ha]
    exact (canonical6026 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA242 + difference 3 2) (sourceB242 + difference 2 3) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5088) := by
    have ha : (tripleCharges (sourceA242 + difference 3 2) (sourceB242 + difference 2 3) sourceC242) = raw6027 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6027; decide +kernel
    rw [ha]
    exact (canonical6027 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA242 + difference 3 4) (sourceB242 + difference 4 3) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA242 + difference 3 4) (sourceB242 + difference 4 3) sourceC242) = raw6028 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6028; decide +kernel
    rw [ha]
    exact (canonical6028 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA242 + difference 3 5) (sourceB242 + difference 5 3) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5106) := by
    have ha : (tripleCharges (sourceA242 + difference 3 5) (sourceB242 + difference 5 3) sourceC242) = raw6029 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6029; decide +kernel
    rw [ha]
    exact (canonical6029 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA242 + difference 4 0) (sourceB242 + difference 0 4) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA242 + difference 4 0) (sourceB242 + difference 0 4) sourceC242) = raw6030 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6030; decide +kernel
    rw [ha]
    exact (canonical6030 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA242 + difference 4 1) (sourceB242 + difference 1 4) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4479) := by
    have ha : (tripleCharges (sourceA242 + difference 4 1) (sourceB242 + difference 1 4) sourceC242) = raw6031 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6031; decide +kernel
    rw [ha]
    exact (canonical6031 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA242 + difference 4 2) (sourceB242 + difference 2 4) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4477) := by
    have ha : (tripleCharges (sourceA242 + difference 4 2) (sourceB242 + difference 2 4) sourceC242) = raw6032 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6032; decide +kernel
    rw [ha]
    exact (canonical6032 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA242 + difference 4 3) (sourceB242 + difference 3 4) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4477) := by
    have ha : (tripleCharges (sourceA242 + difference 4 3) (sourceB242 + difference 3 4) sourceC242) = raw6033 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6033; decide +kernel
    rw [ha]
    exact (canonical6033 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA242 + difference 4 5) (sourceB242 + difference 5 4) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4504) := by
    have ha : (tripleCharges (sourceA242 + difference 4 5) (sourceB242 + difference 5 4) sourceC242) = raw6034 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6034; decide +kernel
    rw [ha]
    exact (canonical6034 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA242 + difference 5 0) (sourceB242 + difference 0 5) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA242 + difference 5 0) (sourceB242 + difference 0 5) sourceC242) = raw6035 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6035; decide +kernel
    rw [ha]
    exact (canonical6035 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA242 + difference 5 1) (sourceB242 + difference 1 5) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA242 + difference 5 1) (sourceB242 + difference 1 5) sourceC242) = raw6036 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6036; decide +kernel
    rw [ha]
    exact (canonical6036 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA242 + difference 5 2) (sourceB242 + difference 2 5) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA242 + difference 5 2) (sourceB242 + difference 2 5) sourceC242) = raw6037 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6037; decide +kernel
    rw [ha]
    exact (canonical6037 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA242 + difference 5 3) (sourceB242 + difference 3 5) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA242 + difference 5 3) (sourceB242 + difference 3 5) sourceC242) = raw6038 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6038; decide +kernel
    rw [ha]
    exact (canonical6038 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA242 + difference 5 4) (sourceB242 + difference 4 5) sourceC242) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA242 + difference 5 4) (sourceB242 + difference 4 5) sourceC242) = raw6039 := by
      apply Matrix.ext; unfold tripleCharges sourceA242 sourceB242 sourceC242 difference raw6039; decide +kernel
    rw [ha]
    exact (canonical6039 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA242 sourceB242 sourceC242
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm242, Integer.Sparse.eval]
  linarith only [hs]

def sourceA243 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB243 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC243 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm243 : Integer.Sparse Master := [(Sum.inr 1658, 2), (Sum.inr 1659, 1), (Sum.inr 1660, 1), (Sum.inr 1746, 1), (Sum.inr 2207, 2), (Sum.inr 2230, 1), (Sum.inr 2294, 1), (Sum.inr 2674, 2), (Sum.inr 2687, 1), (Sum.inr 2696, 2), (Sum.inr 2706, 2), (Sum.inr 2724, 2), (Sum.inr 2725, 2), (Sum.inr 2743, 1), (Sum.inr 2744, 2), (Sum.inr 2788, 1), (Sum.inr 2789, 1), (Sum.inr 2967, 1), (Sum.inr 3056, 1), (Sum.inr 3079, 2), (Sum.inr 3103, 1)]

theorem sourceEq243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm243 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA243 + difference 0 1) (sourceB243 + difference 1 0) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA243 + difference 0 1) (sourceB243 + difference 1 0) sourceC243) = raw6040 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6040; decide +kernel
    rw [ha]
    exact (canonical6040 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA243 + difference 0 2) (sourceB243 + difference 2 0) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA243 + difference 0 2) (sourceB243 + difference 2 0) sourceC243) = raw6041 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6041; decide +kernel
    rw [ha]
    exact (canonical6041 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA243 + difference 0 3) (sourceB243 + difference 3 0) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA243 + difference 0 3) (sourceB243 + difference 3 0) sourceC243) = raw6042 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6042; decide +kernel
    rw [ha]
    exact (canonical6042 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA243 + difference 0 4) (sourceB243 + difference 4 0) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA243 + difference 0 4) (sourceB243 + difference 4 0) sourceC243) = raw6043 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6043; decide +kernel
    rw [ha]
    exact (canonical6043 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA243 + difference 0 5) (sourceB243 + difference 5 0) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA243 + difference 0 5) (sourceB243 + difference 5 0) sourceC243) = raw6044 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6044; decide +kernel
    rw [ha]
    exact (canonical6044 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA243 + difference 1 0) (sourceB243 + difference 0 1) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA243 + difference 1 0) (sourceB243 + difference 0 1) sourceC243) = raw6045 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6045; decide +kernel
    rw [ha]
    exact (canonical6045 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA243 + difference 1 2) (sourceB243 + difference 2 1) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA243 + difference 1 2) (sourceB243 + difference 2 1) sourceC243) = raw6046 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6046; decide +kernel
    rw [ha]
    exact (canonical6046 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA243 + difference 1 3) (sourceB243 + difference 3 1) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA243 + difference 1 3) (sourceB243 + difference 3 1) sourceC243) = raw6047 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6047; decide +kernel
    rw [ha]
    exact (canonical6047 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA243 + difference 1 4) (sourceB243 + difference 4 1) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA243 + difference 1 4) (sourceB243 + difference 4 1) sourceC243) = raw6048 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6048; decide +kernel
    rw [ha]
    exact (canonical6048 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA243 + difference 1 5) (sourceB243 + difference 5 1) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA243 + difference 1 5) (sourceB243 + difference 5 1) sourceC243) = raw6049 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6049; decide +kernel
    rw [ha]
    exact (canonical6049 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA243 + difference 2 0) (sourceB243 + difference 0 2) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA243 + difference 2 0) (sourceB243 + difference 0 2) sourceC243) = raw6050 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6050; decide +kernel
    rw [ha]
    exact (canonical6050 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA243 + difference 2 1) (sourceB243 + difference 1 2) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2674) := by
    have ha : (tripleCharges (sourceA243 + difference 2 1) (sourceB243 + difference 1 2) sourceC243) = raw6051 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6051; decide +kernel
    rw [ha]
    exact (canonical6051 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA243 + difference 2 3) (sourceB243 + difference 3 2) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2696) := by
    have ha : (tripleCharges (sourceA243 + difference 2 3) (sourceB243 + difference 3 2) sourceC243) = raw6052 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6052; decide +kernel
    rw [ha]
    exact (canonical6052 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA243 + difference 2 4) (sourceB243 + difference 4 2) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA243 + difference 2 4) (sourceB243 + difference 4 2) sourceC243) = raw6053 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6053; decide +kernel
    rw [ha]
    exact (canonical6053 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA243 + difference 2 5) (sourceB243 + difference 5 2) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2725) := by
    have ha : (tripleCharges (sourceA243 + difference 2 5) (sourceB243 + difference 5 2) sourceC243) = raw6054 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6054; decide +kernel
    rw [ha]
    exact (canonical6054 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA243 + difference 3 0) (sourceB243 + difference 0 3) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA243 + difference 3 0) (sourceB243 + difference 0 3) sourceC243) = raw6055 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6055; decide +kernel
    rw [ha]
    exact (canonical6055 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA243 + difference 3 1) (sourceB243 + difference 1 3) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2674) := by
    have ha : (tripleCharges (sourceA243 + difference 3 1) (sourceB243 + difference 1 3) sourceC243) = raw6056 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6056; decide +kernel
    rw [ha]
    exact (canonical6056 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA243 + difference 3 2) (sourceB243 + difference 2 3) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2696) := by
    have ha : (tripleCharges (sourceA243 + difference 3 2) (sourceB243 + difference 2 3) sourceC243) = raw6057 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6057; decide +kernel
    rw [ha]
    exact (canonical6057 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA243 + difference 3 4) (sourceB243 + difference 4 3) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA243 + difference 3 4) (sourceB243 + difference 4 3) sourceC243) = raw6058 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6058; decide +kernel
    rw [ha]
    exact (canonical6058 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA243 + difference 3 5) (sourceB243 + difference 5 3) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2725) := by
    have ha : (tripleCharges (sourceA243 + difference 3 5) (sourceB243 + difference 5 3) sourceC243) = raw6059 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6059; decide +kernel
    rw [ha]
    exact (canonical6059 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA243 + difference 4 0) (sourceB243 + difference 0 4) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA243 + difference 4 0) (sourceB243 + difference 0 4) sourceC243) = raw6060 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6060; decide +kernel
    rw [ha]
    exact (canonical6060 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA243 + difference 4 1) (sourceB243 + difference 1 4) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1660) := by
    have ha : (tripleCharges (sourceA243 + difference 4 1) (sourceB243 + difference 1 4) sourceC243) = raw6061 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6061; decide +kernel
    rw [ha]
    exact (canonical6061 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA243 + difference 4 2) (sourceB243 + difference 2 4) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1658) := by
    have ha : (tripleCharges (sourceA243 + difference 4 2) (sourceB243 + difference 2 4) sourceC243) = raw6062 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6062; decide +kernel
    rw [ha]
    exact (canonical6062 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA243 + difference 4 3) (sourceB243 + difference 3 4) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1658) := by
    have ha : (tripleCharges (sourceA243 + difference 4 3) (sourceB243 + difference 3 4) sourceC243) = raw6063 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6063; decide +kernel
    rw [ha]
    exact (canonical6063 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA243 + difference 4 5) (sourceB243 + difference 5 4) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1659) := by
    have ha : (tripleCharges (sourceA243 + difference 4 5) (sourceB243 + difference 5 4) sourceC243) = raw6064 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6064; decide +kernel
    rw [ha]
    exact (canonical6064 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA243 + difference 5 0) (sourceB243 + difference 0 5) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA243 + difference 5 0) (sourceB243 + difference 0 5) sourceC243) = raw6065 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6065; decide +kernel
    rw [ha]
    exact (canonical6065 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA243 + difference 5 1) (sourceB243 + difference 1 5) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA243 + difference 5 1) (sourceB243 + difference 1 5) sourceC243) = raw6066 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6066; decide +kernel
    rw [ha]
    exact (canonical6066 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA243 + difference 5 2) (sourceB243 + difference 2 5) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA243 + difference 5 2) (sourceB243 + difference 2 5) sourceC243) = raw6067 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6067; decide +kernel
    rw [ha]
    exact (canonical6067 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA243 + difference 5 3) (sourceB243 + difference 3 5) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA243 + difference 5 3) (sourceB243 + difference 3 5) sourceC243) = raw6068 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6068; decide +kernel
    rw [ha]
    exact (canonical6068 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA243 + difference 5 4) (sourceB243 + difference 4 5) sourceC243) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA243 + difference 5 4) (sourceB243 + difference 4 5) sourceC243) = raw6069 := by
      apply Matrix.ext; unfold tripleCharges sourceA243 sourceB243 sourceC243 difference raw6069; decide +kernel
    rw [ha]
    exact (canonical6069 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA243 sourceB243 sourceC243
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm243, Integer.Sparse.eval]
  linarith only [hs]

def sourceA244 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB244 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC244 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm244 : Integer.Sparse Master := [(Sum.inr 1060, 2), (Sum.inr 1061, 1), (Sum.inr 1062, 1), (Sum.inr 1088, 1), (Sum.inr 2496, 2), (Sum.inr 2497, 2), (Sum.inr 2498, 2), (Sum.inr 2516, 2), (Sum.inr 2641, 2), (Sum.inr 2642, 1), (Sum.inr 2643, 1), (Sum.inr 2748, 2), (Sum.inr 2761, 1), (Sum.inr 2765, 1), (Sum.inr 2771, 1), (Sum.inr 2777, 2), (Sum.inr 2778, 1), (Sum.inr 2789, 1), (Sum.inr 3086, 2), (Sum.inr 3110, 1), (Sum.inr 3121, 1)]

theorem sourceEq244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm244 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA244 + difference 0 1) (sourceB244 + difference 1 0) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2771) := by
    have ha : (tripleCharges (sourceA244 + difference 0 1) (sourceB244 + difference 1 0) sourceC244) = raw6070 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6070; decide +kernel
    rw [ha]
    exact (canonical6070 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA244 + difference 0 2) (sourceB244 + difference 2 0) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA244 + difference 0 2) (sourceB244 + difference 2 0) sourceC244) = raw6071 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6071; decide +kernel
    rw [ha]
    exact (canonical6071 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA244 + difference 0 3) (sourceB244 + difference 3 0) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA244 + difference 0 3) (sourceB244 + difference 3 0) sourceC244) = raw6072 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6072; decide +kernel
    rw [ha]
    exact (canonical6072 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA244 + difference 0 4) (sourceB244 + difference 4 0) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA244 + difference 0 4) (sourceB244 + difference 4 0) sourceC244) = raw6073 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6073; decide +kernel
    rw [ha]
    exact (canonical6073 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA244 + difference 0 5) (sourceB244 + difference 5 0) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA244 + difference 0 5) (sourceB244 + difference 5 0) sourceC244) = raw6074 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6074; decide +kernel
    rw [ha]
    exact (canonical6074 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA244 + difference 1 0) (sourceB244 + difference 0 1) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA244 + difference 1 0) (sourceB244 + difference 0 1) sourceC244) = raw6075 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6075; decide +kernel
    rw [ha]
    exact (canonical6075 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA244 + difference 1 2) (sourceB244 + difference 2 1) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA244 + difference 1 2) (sourceB244 + difference 2 1) sourceC244) = raw6076 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6076; decide +kernel
    rw [ha]
    exact (canonical6076 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA244 + difference 1 3) (sourceB244 + difference 3 1) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA244 + difference 1 3) (sourceB244 + difference 3 1) sourceC244) = raw6077 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6077; decide +kernel
    rw [ha]
    exact (canonical6077 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA244 + difference 1 4) (sourceB244 + difference 4 1) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA244 + difference 1 4) (sourceB244 + difference 4 1) sourceC244) = raw6078 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6078; decide +kernel
    rw [ha]
    exact (canonical6078 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA244 + difference 1 5) (sourceB244 + difference 5 1) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA244 + difference 1 5) (sourceB244 + difference 5 1) sourceC244) = raw6079 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6079; decide +kernel
    rw [ha]
    exact (canonical6079 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA244 + difference 2 0) (sourceB244 + difference 0 2) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA244 + difference 2 0) (sourceB244 + difference 0 2) sourceC244) = raw6080 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6080; decide +kernel
    rw [ha]
    exact (canonical6080 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA244 + difference 2 1) (sourceB244 + difference 1 2) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2498) := by
    have ha : (tripleCharges (sourceA244 + difference 2 1) (sourceB244 + difference 1 2) sourceC244) = raw6081 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6081; decide +kernel
    rw [ha]
    exact (canonical6081 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA244 + difference 2 3) (sourceB244 + difference 3 2) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2496) := by
    have ha : (tripleCharges (sourceA244 + difference 2 3) (sourceB244 + difference 3 2) sourceC244) = raw6082 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6082; decide +kernel
    rw [ha]
    exact (canonical6082 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA244 + difference 2 4) (sourceB244 + difference 4 2) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA244 + difference 2 4) (sourceB244 + difference 4 2) sourceC244) = raw6083 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6083; decide +kernel
    rw [ha]
    exact (canonical6083 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA244 + difference 2 5) (sourceB244 + difference 5 2) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA244 + difference 2 5) (sourceB244 + difference 5 2) sourceC244) = raw6084 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6084; decide +kernel
    rw [ha]
    exact (canonical6084 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA244 + difference 3 0) (sourceB244 + difference 0 3) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA244 + difference 3 0) (sourceB244 + difference 0 3) sourceC244) = raw6085 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6085; decide +kernel
    rw [ha]
    exact (canonical6085 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA244 + difference 3 1) (sourceB244 + difference 1 3) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2498) := by
    have ha : (tripleCharges (sourceA244 + difference 3 1) (sourceB244 + difference 1 3) sourceC244) = raw6086 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6086; decide +kernel
    rw [ha]
    exact (canonical6086 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA244 + difference 3 2) (sourceB244 + difference 2 3) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2496) := by
    have ha : (tripleCharges (sourceA244 + difference 3 2) (sourceB244 + difference 2 3) sourceC244) = raw6087 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6087; decide +kernel
    rw [ha]
    exact (canonical6087 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA244 + difference 3 4) (sourceB244 + difference 4 3) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA244 + difference 3 4) (sourceB244 + difference 4 3) sourceC244) = raw6088 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6088; decide +kernel
    rw [ha]
    exact (canonical6088 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA244 + difference 3 5) (sourceB244 + difference 5 3) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA244 + difference 3 5) (sourceB244 + difference 5 3) sourceC244) = raw6089 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6089; decide +kernel
    rw [ha]
    exact (canonical6089 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA244 + difference 4 0) (sourceB244 + difference 0 4) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA244 + difference 4 0) (sourceB244 + difference 0 4) sourceC244) = raw6090 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6090; decide +kernel
    rw [ha]
    exact (canonical6090 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA244 + difference 4 1) (sourceB244 + difference 1 4) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1062) := by
    have ha : (tripleCharges (sourceA244 + difference 4 1) (sourceB244 + difference 1 4) sourceC244) = raw6091 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6091; decide +kernel
    rw [ha]
    exact (canonical6091 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA244 + difference 4 2) (sourceB244 + difference 2 4) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1060) := by
    have ha : (tripleCharges (sourceA244 + difference 4 2) (sourceB244 + difference 2 4) sourceC244) = raw6092 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6092; decide +kernel
    rw [ha]
    exact (canonical6092 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA244 + difference 4 3) (sourceB244 + difference 3 4) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1060) := by
    have ha : (tripleCharges (sourceA244 + difference 4 3) (sourceB244 + difference 3 4) sourceC244) = raw6093 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6093; decide +kernel
    rw [ha]
    exact (canonical6093 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA244 + difference 4 5) (sourceB244 + difference 5 4) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1088) := by
    have ha : (tripleCharges (sourceA244 + difference 4 5) (sourceB244 + difference 5 4) sourceC244) = raw6094 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6094; decide +kernel
    rw [ha]
    exact (canonical6094 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA244 + difference 5 0) (sourceB244 + difference 0 5) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2642) := by
    have ha : (tripleCharges (sourceA244 + difference 5 0) (sourceB244 + difference 0 5) sourceC244) = raw6095 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6095; decide +kernel
    rw [ha]
    exact (canonical6095 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA244 + difference 5 1) (sourceB244 + difference 1 5) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA244 + difference 5 1) (sourceB244 + difference 1 5) sourceC244) = raw6096 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6096; decide +kernel
    rw [ha]
    exact (canonical6096 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA244 + difference 5 2) (sourceB244 + difference 2 5) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2641) := by
    have ha : (tripleCharges (sourceA244 + difference 5 2) (sourceB244 + difference 2 5) sourceC244) = raw6097 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6097; decide +kernel
    rw [ha]
    exact (canonical6097 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA244 + difference 5 3) (sourceB244 + difference 3 5) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2641) := by
    have ha : (tripleCharges (sourceA244 + difference 5 3) (sourceB244 + difference 3 5) sourceC244) = raw6098 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6098; decide +kernel
    rw [ha]
    exact (canonical6098 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA244 + difference 5 4) (sourceB244 + difference 4 5) sourceC244) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA244 + difference 5 4) (sourceB244 + difference 4 5) sourceC244) = raw6099 := by
      apply Matrix.ext; unfold tripleCharges sourceA244 sourceB244 sourceC244 difference raw6099; decide +kernel
    rw [ha]
    exact (canonical6099 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA244 sourceB244 sourceC244
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm244, Integer.Sparse.eval]
  linarith only [hs]

def sourceA245 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB245 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC245 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm245 : Integer.Sparse Master := [(Sum.inr 2603, 1), (Sum.inr 3050, 2), (Sum.inr 3052, 1), (Sum.inr 3056, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

theorem sourceEq245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm245 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA245 + difference 0 0) (sourceB245 + difference 0 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA245 + difference 0 0) (sourceB245 + difference 0 0) sourceC245) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA245 + difference 0 1) (sourceB245 + difference 1 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA245 + difference 0 1) (sourceB245 + difference 1 0) sourceC245) = raw6101 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6101; decide +kernel
    rw [ha]
    exact (canonical6101 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA245 + difference 0 2) (sourceB245 + difference 2 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA245 + difference 0 2) (sourceB245 + difference 2 0) sourceC245) = raw6102 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6102; decide +kernel
    rw [ha]
    exact (canonical6102 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA245 + difference 0 3) (sourceB245 + difference 3 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA245 + difference 0 3) (sourceB245 + difference 3 0) sourceC245) = raw6103 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6103; decide +kernel
    rw [ha]
    exact (canonical6103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA245 + difference 0 4) (sourceB245 + difference 4 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA245 + difference 0 4) (sourceB245 + difference 4 0) sourceC245) = raw6104 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6104; decide +kernel
    rw [ha]
    exact (canonical6104 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA245 + difference 0 5) (sourceB245 + difference 5 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2603) := by
    have ha : (tripleCharges (sourceA245 + difference 0 5) (sourceB245 + difference 5 0) sourceC245) = raw6105 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6105; decide +kernel
    rw [ha]
    exact (canonical6105 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA245 + sourceB245) sourceC245) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA245 + sourceB245) sourceC245) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA245 sourceB245 sourceC245 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA245 sourceB245 sourceC245
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm245, Integer.Sparse.eval]
  linarith only [hs]

def sourceA246 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB246 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC246 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm246 : Integer.Sparse Master := [(Sum.inr 1374, 1), (Sum.inr 2888, 1), (Sum.inr 2978, 2), (Sum.inr 3052, 1), (Sum.inr 3056, 1), (Sum.inr 4084, -1)]

theorem sourceEq246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm246 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA246 + difference 0 1) (sourceB246 + difference 1 0) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA246 + difference 0 1) (sourceB246 + difference 1 0) sourceC246) = raw6101 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6101; decide +kernel
    rw [ha]
    exact (canonical6101 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA246 + difference 1 1) (sourceB246 + difference 1 1) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA246 + difference 1 1) (sourceB246 + difference 1 1) sourceC246) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA246 + difference 2 1) (sourceB246 + difference 1 2) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2978) := by
    have ha : (tripleCharges (sourceA246 + difference 2 1) (sourceB246 + difference 1 2) sourceC246) = raw6106 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6106; decide +kernel
    rw [ha]
    exact (canonical6106 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA246 + difference 3 1) (sourceB246 + difference 1 3) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2978) := by
    have ha : (tripleCharges (sourceA246 + difference 3 1) (sourceB246 + difference 1 3) sourceC246) = raw6107 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6107; decide +kernel
    rw [ha]
    exact (canonical6107 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA246 + difference 4 1) (sourceB246 + difference 1 4) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1374) := by
    have ha : (tripleCharges (sourceA246 + difference 4 1) (sourceB246 + difference 1 4) sourceC246) = raw6108 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6108; decide +kernel
    rw [ha]
    exact (canonical6108 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA246 + difference 5 1) (sourceB246 + difference 1 5) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA246 + difference 5 1) (sourceB246 + difference 1 5) sourceC246) = raw6109 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6109; decide +kernel
    rw [ha]
    exact (canonical6109 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA246 + sourceB246) sourceC246) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA246 + sourceB246) sourceC246) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA246 sourceB246 sourceC246 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA246 sourceB246 sourceC246
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm246, Integer.Sparse.eval]
  linarith only [hs]

def sourceA247 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB247 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC247 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm247 : Integer.Sparse Master := [(Sum.inr 2035, 1), (Sum.inr 2597, 1), (Sum.inr 2973, 1), (Sum.inr 2978, 1), (Sum.inr 3052, 1), (Sum.inr 3540, 1), (Sum.inr 4084, -1)]

theorem sourceEq247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm247 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA247 + difference 2 0) (sourceB247 + difference 0 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA247 + difference 2 0) (sourceB247 + difference 0 2) sourceC247) = raw6110 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6110; decide +kernel
    rw [ha]
    exact (canonical6110 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA247 + difference 2 1) (sourceB247 + difference 1 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2978) := by
    have ha : (tripleCharges (sourceA247 + difference 2 1) (sourceB247 + difference 1 2) sourceC247) = raw6106 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6106; decide +kernel
    rw [ha]
    exact (canonical6106 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA247 + difference 2 2) (sourceB247 + difference 2 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA247 + difference 2 2) (sourceB247 + difference 2 2) sourceC247) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA247 + difference 2 3) (sourceB247 + difference 3 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2973) := by
    have ha : (tripleCharges (sourceA247 + difference 2 3) (sourceB247 + difference 3 2) sourceC247) = raw6111 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6111; decide +kernel
    rw [ha]
    exact (canonical6111 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA247 + difference 2 4) (sourceB247 + difference 4 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA247 + difference 2 4) (sourceB247 + difference 4 2) sourceC247) = raw6112 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6112; decide +kernel
    rw [ha]
    exact (canonical6112 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA247 + difference 2 5) (sourceB247 + difference 5 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2597) := by
    have ha : (tripleCharges (sourceA247 + difference 2 5) (sourceB247 + difference 5 2) sourceC247) = raw6113 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6113; decide +kernel
    rw [ha]
    exact (canonical6113 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA247 + sourceB247) sourceC247) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA247 + sourceB247) sourceC247) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA247 sourceB247 sourceC247 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA247 sourceB247 sourceC247
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm247, Integer.Sparse.eval]
  linarith only [hs]

def sourceA248 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB248 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC248 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm248 : Integer.Sparse Master := [(Sum.inr 1365, 1), (Sum.inr 2879, 1), (Sum.inr 2973, 1), (Sum.inr 3050, 1), (Sum.inr 3052, 2), (Sum.inr 4084, -1)]

theorem sourceEq248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm248 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA248 + difference 0 2) (sourceB248 + difference 2 0) sourceC248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA248 + difference 0 2) (sourceB248 + difference 2 0) sourceC248) = raw6102 := by
      apply Matrix.ext; unfold tripleCharges sourceA248 sourceB248 sourceC248 difference raw6102; decide +kernel
    rw [ha]
    exact (canonical6102 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA248 + difference 1 2) (sourceB248 + difference 2 1) sourceC248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA248 + difference 1 2) (sourceB248 + difference 2 1) sourceC248) = raw6114 := by
      apply Matrix.ext; unfold tripleCharges sourceA248 sourceB248 sourceC248 difference raw6114; decide +kernel
    rw [ha]
    exact (canonical6114 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA248 + difference 2 2) (sourceB248 + difference 2 2) sourceC248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA248 + difference 2 2) (sourceB248 + difference 2 2) sourceC248) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA248 sourceB248 sourceC248 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA248 + difference 3 2) (sourceB248 + difference 2 3) sourceC248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2973) := by
    have ha : (tripleCharges (sourceA248 + difference 3 2) (sourceB248 + difference 2 3) sourceC248) = raw6115 := by
      apply Matrix.ext; unfold tripleCharges sourceA248 sourceB248 sourceC248 difference raw6115; decide +kernel
    rw [ha]
    exact (canonical6115 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA248 + difference 4 2) (sourceB248 + difference 2 4) sourceC248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1365) := by
    have ha : (tripleCharges (sourceA248 + difference 4 2) (sourceB248 + difference 2 4) sourceC248) = raw6116 := by
      apply Matrix.ext; unfold tripleCharges sourceA248 sourceB248 sourceC248 difference raw6116; decide +kernel
    rw [ha]
    exact (canonical6116 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA248 + difference 5 2) (sourceB248 + difference 2 5) sourceC248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA248 + difference 5 2) (sourceB248 + difference 2 5) sourceC248) = raw6117 := by
      apply Matrix.ext; unfold tripleCharges sourceA248 sourceB248 sourceC248 difference raw6117; decide +kernel
    rw [ha]
    exact (canonical6117 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA248 + sourceB248) sourceC248) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA248 + sourceB248) sourceC248) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA248 sourceB248 sourceC248 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA248 sourceB248 sourceC248
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm248, Integer.Sparse.eval]
  linarith only [hs]

def sourceA249 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB249 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC249 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm249 : Integer.Sparse Master := [(Sum.inr 1365, 2), (Sum.inr 1369, 1), (Sum.inr 1374, 1), (Sum.inr 1434, 1), (Sum.inr 3052, 1), (Sum.inr 4084, -1)]

theorem sourceEq249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm249 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA249 + difference 4 0) (sourceB249 + difference 0 4) sourceC249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA249 + difference 4 0) (sourceB249 + difference 0 4) sourceC249) = raw6118 := by
      apply Matrix.ext; unfold tripleCharges sourceA249 sourceB249 sourceC249 difference raw6118; decide +kernel
    rw [ha]
    exact (canonical6118 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA249 + difference 4 1) (sourceB249 + difference 1 4) sourceC249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1374) := by
    have ha : (tripleCharges (sourceA249 + difference 4 1) (sourceB249 + difference 1 4) sourceC249) = raw6108 := by
      apply Matrix.ext; unfold tripleCharges sourceA249 sourceB249 sourceC249 difference raw6108; decide +kernel
    rw [ha]
    exact (canonical6108 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA249 + difference 4 2) (sourceB249 + difference 2 4) sourceC249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1365) := by
    have ha : (tripleCharges (sourceA249 + difference 4 2) (sourceB249 + difference 2 4) sourceC249) = raw6116 := by
      apply Matrix.ext; unfold tripleCharges sourceA249 sourceB249 sourceC249 difference raw6116; decide +kernel
    rw [ha]
    exact (canonical6116 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA249 + difference 4 3) (sourceB249 + difference 3 4) sourceC249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1365) := by
    have ha : (tripleCharges (sourceA249 + difference 4 3) (sourceB249 + difference 3 4) sourceC249) = raw6119 := by
      apply Matrix.ext; unfold tripleCharges sourceA249 sourceB249 sourceC249 difference raw6119; decide +kernel
    rw [ha]
    exact (canonical6119 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA249 + difference 4 4) (sourceB249 + difference 4 4) sourceC249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA249 + difference 4 4) (sourceB249 + difference 4 4) sourceC249) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA249 sourceB249 sourceC249 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA249 + difference 4 5) (sourceB249 + difference 5 4) sourceC249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1434) := by
    have ha : (tripleCharges (sourceA249 + difference 4 5) (sourceB249 + difference 5 4) sourceC249) = raw6120 := by
      apply Matrix.ext; unfold tripleCharges sourceA249 sourceB249 sourceC249 difference raw6120; decide +kernel
    rw [ha]
    exact (canonical6120 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA249 + sourceB249) sourceC249) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA249 + sourceB249) sourceC249) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA249 sourceB249 sourceC249 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA249 sourceB249 sourceC249
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm249, Integer.Sparse.eval]
  linarith only [hs]

def sourceA250 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB250 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC250 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm250 : Integer.Sparse Master := [(Sum.inr 3052, 1), (Sum.inr 3540, 2), (Sum.inr 3548, 1), (Sum.inr 3582, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

theorem sourceEq250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm250 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA250 + difference 0 4) (sourceB250 + difference 4 0) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA250 + difference 0 4) (sourceB250 + difference 4 0) sourceC250) = raw6104 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6104; decide +kernel
    rw [ha]
    exact (canonical6104 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA250 + difference 1 4) (sourceB250 + difference 4 1) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA250 + difference 1 4) (sourceB250 + difference 4 1) sourceC250) = raw6121 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6121; decide +kernel
    rw [ha]
    exact (canonical6121 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA250 + difference 2 4) (sourceB250 + difference 4 2) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA250 + difference 2 4) (sourceB250 + difference 4 2) sourceC250) = raw6112 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6112; decide +kernel
    rw [ha]
    exact (canonical6112 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA250 + difference 3 4) (sourceB250 + difference 4 3) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA250 + difference 3 4) (sourceB250 + difference 4 3) sourceC250) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA250 + difference 4 4) (sourceB250 + difference 4 4) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA250 + difference 4 4) (sourceB250 + difference 4 4) sourceC250) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA250 + difference 5 4) (sourceB250 + difference 4 5) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA250 + difference 5 4) (sourceB250 + difference 4 5) sourceC250) = raw6123 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6123; decide +kernel
    rw [ha]
    exact (canonical6123 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA250 + sourceB250) sourceC250) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA250 + sourceB250) sourceC250) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA250 sourceB250 sourceC250 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA250 sourceB250 sourceC250
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm250, Integer.Sparse.eval]
  linarith only [hs]

def sourceA251 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB251 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC251 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm251 : Integer.Sparse Master := [(Sum.inr 2062, 1), (Sum.inr 2879, 2), (Sum.inr 2888, 1), (Sum.inr 3052, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

theorem sourceEq251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm251 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA251 + difference 5 0) (sourceB251 + difference 0 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA251 + difference 5 0) (sourceB251 + difference 0 5) sourceC251) = raw6124 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6124; decide +kernel
    rw [ha]
    exact (canonical6124 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA251 + difference 5 1) (sourceB251 + difference 1 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA251 + difference 5 1) (sourceB251 + difference 1 5) sourceC251) = raw6109 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6109; decide +kernel
    rw [ha]
    exact (canonical6109 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA251 + difference 5 2) (sourceB251 + difference 2 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA251 + difference 5 2) (sourceB251 + difference 2 5) sourceC251) = raw6117 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6117; decide +kernel
    rw [ha]
    exact (canonical6117 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA251 + difference 5 3) (sourceB251 + difference 3 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA251 + difference 5 3) (sourceB251 + difference 3 5) sourceC251) = raw6125 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6125; decide +kernel
    rw [ha]
    exact (canonical6125 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA251 + difference 5 4) (sourceB251 + difference 4 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA251 + difference 5 4) (sourceB251 + difference 4 5) sourceC251) = raw6123 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6123; decide +kernel
    rw [ha]
    exact (canonical6123 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA251 + difference 5 5) (sourceB251 + difference 5 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA251 + difference 5 5) (sourceB251 + difference 5 5) sourceC251) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA251 + sourceB251) sourceC251) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA251 + sourceB251) sourceC251) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA251 sourceB251 sourceC251 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA251 sourceB251 sourceC251
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm251, Integer.Sparse.eval]
  linarith only [hs]

def sourceA252 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB252 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC252 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm252 : Integer.Sparse Master := [(Sum.inr 4587, 1), (Sum.inr 4588, 1), (Sum.inr 4592, 1), (Sum.inr 4597, 1), (Sum.inr 4607, 1), (Sum.inr 4824, 1), (Sum.inr 4829, 1), (Sum.inr 4836, 1), (Sum.inr 4853, 1), (Sum.inr 5074, 1), (Sum.inr 5080, 1), (Sum.inr 5105, 1), (Sum.inr 5129, 1), (Sum.inr 5138, 1), (Sum.inr 5146, 1), (Sum.inr 5186, 1), (Sum.inr 5188, 1), (Sum.inr 5200, 1), (Sum.inr 5254, 1), (Sum.inr 5256, 1), (Sum.inr 5258, 1), (Sum.inr 5267, 1), (Sum.inr 5271, 1), (Sum.inr 5287, 1), (Sum.inr 5289, 1), (Sum.inr 5411, 1), (Sum.inr 5412, 1), (Sum.inr 5425, 1), (Sum.inr 5434, 1), (Sum.inr 5436, 1)]

theorem sourceEq252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm252 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA252 + difference 0 1) (sourceB252 + difference 1 0) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA252 + difference 0 1) (sourceB252 + difference 1 0) sourceC252) = raw6126 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6126; decide +kernel
    rw [ha]
    exact (canonical6126 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA252 + difference 0 2) (sourceB252 + difference 2 0) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA252 + difference 0 2) (sourceB252 + difference 2 0) sourceC252) = raw6127 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6127; decide +kernel
    rw [ha]
    exact (canonical6127 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA252 + difference 0 3) (sourceB252 + difference 3 0) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA252 + difference 0 3) (sourceB252 + difference 3 0) sourceC252) = raw6128 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6128; decide +kernel
    rw [ha]
    exact (canonical6128 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA252 + difference 0 4) (sourceB252 + difference 4 0) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA252 + difference 0 4) (sourceB252 + difference 4 0) sourceC252) = raw6129 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6129; decide +kernel
    rw [ha]
    exact (canonical6129 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA252 + difference 0 5) (sourceB252 + difference 5 0) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA252 + difference 0 5) (sourceB252 + difference 5 0) sourceC252) = raw6130 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6130; decide +kernel
    rw [ha]
    exact (canonical6130 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA252 + difference 1 0) (sourceB252 + difference 0 1) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4597) := by
    have ha : (tripleCharges (sourceA252 + difference 1 0) (sourceB252 + difference 0 1) sourceC252) = raw6131 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6131; decide +kernel
    rw [ha]
    exact (canonical6131 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA252 + difference 1 2) (sourceB252 + difference 2 1) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5146) := by
    have ha : (tripleCharges (sourceA252 + difference 1 2) (sourceB252 + difference 2 1) sourceC252) = raw6132 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6132; decide +kernel
    rw [ha]
    exact (canonical6132 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA252 + difference 1 3) (sourceB252 + difference 3 1) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5200) := by
    have ha : (tripleCharges (sourceA252 + difference 1 3) (sourceB252 + difference 3 1) sourceC252) = raw6133 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6133; decide +kernel
    rw [ha]
    exact (canonical6133 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA252 + difference 1 4) (sourceB252 + difference 4 1) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA252 + difference 1 4) (sourceB252 + difference 4 1) sourceC252) = raw6134 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6134; decide +kernel
    rw [ha]
    exact (canonical6134 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA252 + difference 1 5) (sourceB252 + difference 5 1) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA252 + difference 1 5) (sourceB252 + difference 5 1) sourceC252) = raw6135 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6135; decide +kernel
    rw [ha]
    exact (canonical6135 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA252 + difference 2 0) (sourceB252 + difference 0 2) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4587) := by
    have ha : (tripleCharges (sourceA252 + difference 2 0) (sourceB252 + difference 0 2) sourceC252) = raw6136 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6136; decide +kernel
    rw [ha]
    exact (canonical6136 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA252 + difference 2 1) (sourceB252 + difference 1 2) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA252 + difference 2 1) (sourceB252 + difference 1 2) sourceC252) = raw6137 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6137; decide +kernel
    rw [ha]
    exact (canonical6137 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA252 + difference 2 3) (sourceB252 + difference 3 2) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5186) := by
    have ha : (tripleCharges (sourceA252 + difference 2 3) (sourceB252 + difference 3 2) sourceC252) = raw6138 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6138; decide +kernel
    rw [ha]
    exact (canonical6138 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA252 + difference 2 4) (sourceB252 + difference 4 2) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA252 + difference 2 4) (sourceB252 + difference 4 2) sourceC252) = raw6139 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6139; decide +kernel
    rw [ha]
    exact (canonical6139 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA252 + difference 2 5) (sourceB252 + difference 5 2) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA252 + difference 2 5) (sourceB252 + difference 5 2) sourceC252) = raw6140 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6140; decide +kernel
    rw [ha]
    exact (canonical6140 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA252 + difference 3 0) (sourceB252 + difference 0 3) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA252 + difference 3 0) (sourceB252 + difference 0 3) sourceC252) = raw6141 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6141; decide +kernel
    rw [ha]
    exact (canonical6141 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA252 + difference 3 1) (sourceB252 + difference 1 3) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA252 + difference 3 1) (sourceB252 + difference 1 3) sourceC252) = raw6142 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6142; decide +kernel
    rw [ha]
    exact (canonical6142 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA252 + difference 3 2) (sourceB252 + difference 2 3) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA252 + difference 3 2) (sourceB252 + difference 2 3) sourceC252) = raw6143 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6143; decide +kernel
    rw [ha]
    exact (canonical6143 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA252 + difference 3 4) (sourceB252 + difference 4 3) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA252 + difference 3 4) (sourceB252 + difference 4 3) sourceC252) = raw6144 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6144; decide +kernel
    rw [ha]
    exact (canonical6144 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA252 + difference 3 5) (sourceB252 + difference 5 3) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA252 + difference 3 5) (sourceB252 + difference 5 3) sourceC252) = raw6145 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6145; decide +kernel
    rw [ha]
    exact (canonical6145 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA252 + difference 4 0) (sourceB252 + difference 0 4) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA252 + difference 4 0) (sourceB252 + difference 0 4) sourceC252) = raw6146 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6146; decide +kernel
    rw [ha]
    exact (canonical6146 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA252 + difference 4 1) (sourceB252 + difference 1 4) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA252 + difference 4 1) (sourceB252 + difference 1 4) sourceC252) = raw6147 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6147; decide +kernel
    rw [ha]
    exact (canonical6147 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA252 + difference 4 2) (sourceB252 + difference 2 4) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA252 + difference 4 2) (sourceB252 + difference 2 4) sourceC252) = raw6148 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6148; decide +kernel
    rw [ha]
    exact (canonical6148 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA252 + difference 4 3) (sourceB252 + difference 3 4) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA252 + difference 4 3) (sourceB252 + difference 3 4) sourceC252) = raw6149 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6149; decide +kernel
    rw [ha]
    exact (canonical6149 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA252 + difference 4 5) (sourceB252 + difference 5 4) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA252 + difference 4 5) (sourceB252 + difference 5 4) sourceC252) = raw6150 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6150; decide +kernel
    rw [ha]
    exact (canonical6150 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA252 + difference 5 0) (sourceB252 + difference 0 5) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4588) := by
    have ha : (tripleCharges (sourceA252 + difference 5 0) (sourceB252 + difference 0 5) sourceC252) = raw6151 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6151; decide +kernel
    rw [ha]
    exact (canonical6151 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA252 + difference 5 1) (sourceB252 + difference 1 5) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA252 + difference 5 1) (sourceB252 + difference 1 5) sourceC252) = raw6152 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6152; decide +kernel
    rw [ha]
    exact (canonical6152 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA252 + difference 5 2) (sourceB252 + difference 2 5) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4824) := by
    have ha : (tripleCharges (sourceA252 + difference 5 2) (sourceB252 + difference 2 5) sourceC252) = raw6153 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6153; decide +kernel
    rw [ha]
    exact (canonical6153 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA252 + difference 5 3) (sourceB252 + difference 3 5) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4829) := by
    have ha : (tripleCharges (sourceA252 + difference 5 3) (sourceB252 + difference 3 5) sourceC252) = raw6154 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6154; decide +kernel
    rw [ha]
    exact (canonical6154 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA252 + difference 5 4) (sourceB252 + difference 4 5) sourceC252) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA252 + difference 5 4) (sourceB252 + difference 4 5) sourceC252) = raw6155 := by
      apply Matrix.ext; unfold tripleCharges sourceA252 sourceB252 sourceC252 difference raw6155; decide +kernel
    rw [ha]
    exact (canonical6155 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA252 sourceB252 sourceC252
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm252, Integer.Sparse.eval]
  linarith only [hs]

def sourceA253 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB253 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC253 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm253 : Integer.Sparse Master := [(Sum.inr 1210, 1), (Sum.inr 1211, 1), (Sum.inr 1219, 1), (Sum.inr 1230, 1), (Sum.inr 1261, 1), (Sum.inr 2071, 1), (Sum.inr 2080, 1), (Sum.inr 2090, 1), (Sum.inr 2197, 1), (Sum.inr 2860, 1), (Sum.inr 2867, 1), (Sum.inr 2876, 1), (Sum.inr 2916, 1), (Sum.inr 2922, 1), (Sum.inr 2933, 1), (Sum.inr 2984, 1), (Sum.inr 2990, 1), (Sum.inr 2997, 1), (Sum.inr 3016, 1), (Sum.inr 3025, 1), (Sum.inr 3038, 1), (Sum.inr 3085, 1), (Sum.inr 3089, 1), (Sum.inr 3097, 1), (Sum.inr 3109, 1), (Sum.inr 3814, 1), (Sum.inr 3872, 1), (Sum.inr 3877, 1), (Sum.inr 3883, 1), (Sum.inr 3982, 1)]

theorem sourceEq253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm253 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA253 + difference 0 1) (sourceB253 + difference 1 0) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA253 + difference 0 1) (sourceB253 + difference 1 0) sourceC253) = raw6156 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6156; decide +kernel
    rw [ha]
    exact (canonical6156 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA253 + difference 0 2) (sourceB253 + difference 2 0) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA253 + difference 0 2) (sourceB253 + difference 2 0) sourceC253) = raw6157 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6157; decide +kernel
    rw [ha]
    exact (canonical6157 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA253 + difference 0 3) (sourceB253 + difference 3 0) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA253 + difference 0 3) (sourceB253 + difference 3 0) sourceC253) = raw6158 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6158; decide +kernel
    rw [ha]
    exact (canonical6158 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA253 + difference 0 4) (sourceB253 + difference 4 0) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA253 + difference 0 4) (sourceB253 + difference 4 0) sourceC253) = raw6159 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6159; decide +kernel
    rw [ha]
    exact (canonical6159 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA253 + difference 0 5) (sourceB253 + difference 5 0) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA253 + difference 0 5) (sourceB253 + difference 5 0) sourceC253) = raw6160 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6160; decide +kernel
    rw [ha]
    exact (canonical6160 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA253 + difference 1 0) (sourceB253 + difference 0 1) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1230) := by
    have ha : (tripleCharges (sourceA253 + difference 1 0) (sourceB253 + difference 0 1) sourceC253) = raw6161 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6161; decide +kernel
    rw [ha]
    exact (canonical6161 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA253 + difference 1 2) (sourceB253 + difference 2 1) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2922) := by
    have ha : (tripleCharges (sourceA253 + difference 1 2) (sourceB253 + difference 2 1) sourceC253) = raw6162 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6162; decide +kernel
    rw [ha]
    exact (canonical6162 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA253 + difference 1 3) (sourceB253 + difference 3 1) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2876) := by
    have ha : (tripleCharges (sourceA253 + difference 1 3) (sourceB253 + difference 3 1) sourceC253) = raw6163 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6163; decide +kernel
    rw [ha]
    exact (canonical6163 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA253 + difference 1 4) (sourceB253 + difference 4 1) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA253 + difference 1 4) (sourceB253 + difference 4 1) sourceC253) = raw6164 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6164; decide +kernel
    rw [ha]
    exact (canonical6164 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA253 + difference 1 5) (sourceB253 + difference 5 1) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA253 + difference 1 5) (sourceB253 + difference 5 1) sourceC253) = raw6165 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6165; decide +kernel
    rw [ha]
    exact (canonical6165 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA253 + difference 2 0) (sourceB253 + difference 0 2) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA253 + difference 2 0) (sourceB253 + difference 0 2) sourceC253) = raw6166 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6166; decide +kernel
    rw [ha]
    exact (canonical6166 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA253 + difference 2 1) (sourceB253 + difference 1 2) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA253 + difference 2 1) (sourceB253 + difference 1 2) sourceC253) = raw6167 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6167; decide +kernel
    rw [ha]
    exact (canonical6167 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA253 + difference 2 3) (sourceB253 + difference 3 2) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2860) := by
    have ha : (tripleCharges (sourceA253 + difference 2 3) (sourceB253 + difference 3 2) sourceC253) = raw6168 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6168; decide +kernel
    rw [ha]
    exact (canonical6168 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA253 + difference 2 4) (sourceB253 + difference 4 2) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA253 + difference 2 4) (sourceB253 + difference 4 2) sourceC253) = raw6169 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6169; decide +kernel
    rw [ha]
    exact (canonical6169 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA253 + difference 2 5) (sourceB253 + difference 5 2) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA253 + difference 2 5) (sourceB253 + difference 5 2) sourceC253) = raw6170 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6170; decide +kernel
    rw [ha]
    exact (canonical6170 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA253 + difference 3 0) (sourceB253 + difference 0 3) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA253 + difference 3 0) (sourceB253 + difference 0 3) sourceC253) = raw6171 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6171; decide +kernel
    rw [ha]
    exact (canonical6171 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA253 + difference 3 1) (sourceB253 + difference 1 3) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2997) := by
    have ha : (tripleCharges (sourceA253 + difference 3 1) (sourceB253 + difference 1 3) sourceC253) = raw6172 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6172; decide +kernel
    rw [ha]
    exact (canonical6172 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA253 + difference 3 2) (sourceB253 + difference 2 3) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA253 + difference 3 2) (sourceB253 + difference 2 3) sourceC253) = raw6173 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6173; decide +kernel
    rw [ha]
    exact (canonical6173 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA253 + difference 3 4) (sourceB253 + difference 4 3) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA253 + difference 3 4) (sourceB253 + difference 4 3) sourceC253) = raw6174 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6174; decide +kernel
    rw [ha]
    exact (canonical6174 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA253 + difference 3 5) (sourceB253 + difference 5 3) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA253 + difference 3 5) (sourceB253 + difference 5 3) sourceC253) = raw6175 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6175; decide +kernel
    rw [ha]
    exact (canonical6175 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA253 + difference 4 0) (sourceB253 + difference 0 4) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA253 + difference 4 0) (sourceB253 + difference 0 4) sourceC253) = raw6176 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6176; decide +kernel
    rw [ha]
    exact (canonical6176 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA253 + difference 4 1) (sourceB253 + difference 1 4) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2990) := by
    have ha : (tripleCharges (sourceA253 + difference 4 1) (sourceB253 + difference 1 4) sourceC253) = raw6177 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6177; decide +kernel
    rw [ha]
    exact (canonical6177 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA253 + difference 4 2) (sourceB253 + difference 2 4) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA253 + difference 4 2) (sourceB253 + difference 2 4) sourceC253) = raw6178 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6178; decide +kernel
    rw [ha]
    exact (canonical6178 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA253 + difference 4 3) (sourceB253 + difference 3 4) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA253 + difference 4 3) (sourceB253 + difference 3 4) sourceC253) = raw6179 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6179; decide +kernel
    rw [ha]
    exact (canonical6179 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA253 + difference 4 5) (sourceB253 + difference 5 4) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA253 + difference 4 5) (sourceB253 + difference 5 4) sourceC253) = raw6180 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6180; decide +kernel
    rw [ha]
    exact (canonical6180 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA253 + difference 5 0) (sourceB253 + difference 0 5) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA253 + difference 5 0) (sourceB253 + difference 0 5) sourceC253) = raw6181 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6181; decide +kernel
    rw [ha]
    exact (canonical6181 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA253 + difference 5 1) (sourceB253 + difference 1 5) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA253 + difference 5 1) (sourceB253 + difference 1 5) sourceC253) = raw6182 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6182; decide +kernel
    rw [ha]
    exact (canonical6182 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA253 + difference 5 2) (sourceB253 + difference 2 5) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA253 + difference 5 2) (sourceB253 + difference 2 5) sourceC253) = raw6183 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6183; decide +kernel
    rw [ha]
    exact (canonical6183 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA253 + difference 5 3) (sourceB253 + difference 3 5) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2080) := by
    have ha : (tripleCharges (sourceA253 + difference 5 3) (sourceB253 + difference 3 5) sourceC253) = raw6184 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6184; decide +kernel
    rw [ha]
    exact (canonical6184 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA253 + difference 5 4) (sourceB253 + difference 4 5) sourceC253) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA253 + difference 5 4) (sourceB253 + difference 4 5) sourceC253) = raw6185 := by
      apply Matrix.ext; unfold tripleCharges sourceA253 sourceB253 sourceC253 difference raw6185; decide +kernel
    rw [ha]
    exact (canonical6185 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA253 sourceB253 sourceC253
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm253, Integer.Sparse.eval]
  linarith only [hs]

def sourceA254 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB254 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC254 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm254 : Integer.Sparse Master := [(Sum.inr 2043, 1), (Sum.inr 2045, 1), (Sum.inr 2049, 1), (Sum.inr 2055, 1), (Sum.inr 2259, 1), (Sum.inr 3285, 1), (Sum.inr 3287, 1), (Sum.inr 3295, 1), (Sum.inr 3296, 1), (Sum.inr 3463, 1), (Sum.inr 3478, 1), (Sum.inr 3479, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3525, 1), (Sum.inr 3527, 1), (Sum.inr 3528, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3538, 1), (Sum.inr 3541, 1), (Sum.inr 3560, 1), (Sum.inr 3572, 1), (Sum.inr 3575, 1), (Sum.inr 3577, 1), (Sum.inr 3813, 1), (Sum.inr 3840, 1), (Sum.inr 3852, 1), (Sum.inr 3854, 1), (Sum.inr 3856, 1)]

theorem sourceEq254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm254 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA254 + difference 0 1) (sourceB254 + difference 1 0) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA254 + difference 0 1) (sourceB254 + difference 1 0) sourceC254) = raw6186 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6186; decide +kernel
    rw [ha]
    exact (canonical6186 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA254 + difference 0 2) (sourceB254 + difference 2 0) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA254 + difference 0 2) (sourceB254 + difference 2 0) sourceC254) = raw6187 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6187; decide +kernel
    rw [ha]
    exact (canonical6187 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA254 + difference 0 3) (sourceB254 + difference 3 0) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA254 + difference 0 3) (sourceB254 + difference 3 0) sourceC254) = raw6188 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6188; decide +kernel
    rw [ha]
    exact (canonical6188 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA254 + difference 0 4) (sourceB254 + difference 4 0) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA254 + difference 0 4) (sourceB254 + difference 4 0) sourceC254) = raw6189 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6189; decide +kernel
    rw [ha]
    exact (canonical6189 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA254 + difference 0 5) (sourceB254 + difference 5 0) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA254 + difference 0 5) (sourceB254 + difference 5 0) sourceC254) = raw6190 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6190; decide +kernel
    rw [ha]
    exact (canonical6190 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA254 + difference 1 0) (sourceB254 + difference 0 1) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3287) := by
    have ha : (tripleCharges (sourceA254 + difference 1 0) (sourceB254 + difference 0 1) sourceC254) = raw6191 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6191; decide +kernel
    rw [ha]
    exact (canonical6191 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA254 + difference 1 2) (sourceB254 + difference 2 1) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3560) := by
    have ha : (tripleCharges (sourceA254 + difference 1 2) (sourceB254 + difference 2 1) sourceC254) = raw6192 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6192; decide +kernel
    rw [ha]
    exact (canonical6192 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA254 + difference 1 3) (sourceB254 + difference 3 1) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3575) := by
    have ha : (tripleCharges (sourceA254 + difference 1 3) (sourceB254 + difference 3 1) sourceC254) = raw6193 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6193; decide +kernel
    rw [ha]
    exact (canonical6193 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA254 + difference 1 4) (sourceB254 + difference 4 1) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3577) := by
    have ha : (tripleCharges (sourceA254 + difference 1 4) (sourceB254 + difference 4 1) sourceC254) = raw6194 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6194; decide +kernel
    rw [ha]
    exact (canonical6194 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA254 + difference 1 5) (sourceB254 + difference 5 1) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA254 + difference 1 5) (sourceB254 + difference 5 1) sourceC254) = raw6195 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6195; decide +kernel
    rw [ha]
    exact (canonical6195 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA254 + difference 2 0) (sourceB254 + difference 0 2) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA254 + difference 2 0) (sourceB254 + difference 0 2) sourceC254) = raw6196 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6196; decide +kernel
    rw [ha]
    exact (canonical6196 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA254 + difference 2 1) (sourceB254 + difference 1 2) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA254 + difference 2 1) (sourceB254 + difference 1 2) sourceC254) = raw6197 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6197; decide +kernel
    rw [ha]
    exact (canonical6197 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA254 + difference 2 3) (sourceB254 + difference 3 2) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3527) := by
    have ha : (tripleCharges (sourceA254 + difference 2 3) (sourceB254 + difference 3 2) sourceC254) = raw6198 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6198; decide +kernel
    rw [ha]
    exact (canonical6198 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA254 + difference 2 4) (sourceB254 + difference 4 2) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA254 + difference 2 4) (sourceB254 + difference 4 2) sourceC254) = raw6199 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6199; decide +kernel
    rw [ha]
    exact (canonical6199 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA254 + difference 2 5) (sourceB254 + difference 5 2) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA254 + difference 2 5) (sourceB254 + difference 5 2) sourceC254) = raw6200 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6200; decide +kernel
    rw [ha]
    exact (canonical6200 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA254 + difference 3 0) (sourceB254 + difference 0 3) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA254 + difference 3 0) (sourceB254 + difference 0 3) sourceC254) = raw6201 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6201; decide +kernel
    rw [ha]
    exact (canonical6201 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA254 + difference 3 1) (sourceB254 + difference 1 3) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA254 + difference 3 1) (sourceB254 + difference 1 3) sourceC254) = raw6202 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6202; decide +kernel
    rw [ha]
    exact (canonical6202 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA254 + difference 3 2) (sourceB254 + difference 2 3) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA254 + difference 3 2) (sourceB254 + difference 2 3) sourceC254) = raw6203 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6203; decide +kernel
    rw [ha]
    exact (canonical6203 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA254 + difference 3 4) (sourceB254 + difference 4 3) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA254 + difference 3 4) (sourceB254 + difference 4 3) sourceC254) = raw6204 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6204; decide +kernel
    rw [ha]
    exact (canonical6204 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA254 + difference 3 5) (sourceB254 + difference 5 3) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA254 + difference 3 5) (sourceB254 + difference 5 3) sourceC254) = raw6205 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6205; decide +kernel
    rw [ha]
    exact (canonical6205 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA254 + difference 4 0) (sourceB254 + difference 0 4) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA254 + difference 4 0) (sourceB254 + difference 0 4) sourceC254) = raw6206 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6206; decide +kernel
    rw [ha]
    exact (canonical6206 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA254 + difference 4 1) (sourceB254 + difference 1 4) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA254 + difference 4 1) (sourceB254 + difference 1 4) sourceC254) = raw6207 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6207; decide +kernel
    rw [ha]
    exact (canonical6207 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA254 + difference 4 2) (sourceB254 + difference 2 4) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA254 + difference 4 2) (sourceB254 + difference 2 4) sourceC254) = raw6208 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6208; decide +kernel
    rw [ha]
    exact (canonical6208 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA254 + difference 4 3) (sourceB254 + difference 3 4) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA254 + difference 4 3) (sourceB254 + difference 3 4) sourceC254) = raw6209 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6209; decide +kernel
    rw [ha]
    exact (canonical6209 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA254 + difference 4 5) (sourceB254 + difference 5 4) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA254 + difference 4 5) (sourceB254 + difference 5 4) sourceC254) = raw6210 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6210; decide +kernel
    rw [ha]
    exact (canonical6210 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA254 + difference 5 0) (sourceB254 + difference 0 5) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2045) := by
    have ha : (tripleCharges (sourceA254 + difference 5 0) (sourceB254 + difference 0 5) sourceC254) = raw6211 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6211; decide +kernel
    rw [ha]
    exact (canonical6211 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA254 + difference 5 1) (sourceB254 + difference 1 5) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA254 + difference 5 1) (sourceB254 + difference 1 5) sourceC254) = raw6212 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6212; decide +kernel
    rw [ha]
    exact (canonical6212 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA254 + difference 5 2) (sourceB254 + difference 2 5) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2043) := by
    have ha : (tripleCharges (sourceA254 + difference 5 2) (sourceB254 + difference 2 5) sourceC254) = raw6213 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6213; decide +kernel
    rw [ha]
    exact (canonical6213 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA254 + difference 5 3) (sourceB254 + difference 3 5) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2049) := by
    have ha : (tripleCharges (sourceA254 + difference 5 3) (sourceB254 + difference 3 5) sourceC254) = raw6214 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6214; decide +kernel
    rw [ha]
    exact (canonical6214 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA254 + difference 5 4) (sourceB254 + difference 4 5) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA254 + difference 5 4) (sourceB254 + difference 4 5) sourceC254) = raw6215 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6215; decide +kernel
    rw [ha]
    exact (canonical6215 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA254 sourceB254 sourceC254
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm254, Integer.Sparse.eval]
  linarith only [hs]

def sourceA255 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB255 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC255 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm255 : Integer.Sparse Master := [(Sum.inr 2724, 1), (Sum.inr 3809, 1), (Sum.inr 3814, 1), (Sum.inr 3839, 1), (Sum.inr 3877, 1), (Sum.inr 3903, 1), (Sum.inr 4092, -1)]

theorem sourceEq255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm255 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA255 + difference 0 0) (sourceB255 + difference 0 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA255 + difference 0 0) (sourceB255 + difference 0 0) sourceC255) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA255 + difference 0 1) (sourceB255 + difference 1 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA255 + difference 0 1) (sourceB255 + difference 1 0) sourceC255) = raw6217 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6217; decide +kernel
    rw [ha]
    exact (canonical6217 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA255 + difference 0 2) (sourceB255 + difference 2 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA255 + difference 0 2) (sourceB255 + difference 2 0) sourceC255) = raw6218 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6218; decide +kernel
    rw [ha]
    exact (canonical6218 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA255 + difference 0 3) (sourceB255 + difference 3 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA255 + difference 0 3) (sourceB255 + difference 3 0) sourceC255) = raw6219 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6219; decide +kernel
    rw [ha]
    exact (canonical6219 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA255 + difference 0 4) (sourceB255 + difference 4 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA255 + difference 0 4) (sourceB255 + difference 4 0) sourceC255) = raw6220 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6220; decide +kernel
    rw [ha]
    exact (canonical6220 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA255 + difference 0 5) (sourceB255 + difference 5 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3903) := by
    have ha : (tripleCharges (sourceA255 + difference 0 5) (sourceB255 + difference 5 0) sourceC255) = raw6221 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6221; decide +kernel
    rw [ha]
    exact (canonical6221 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA255 + sourceB255) sourceC255) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA255 + sourceB255) sourceC255) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA255 sourceB255 sourceC255 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA255 sourceB255 sourceC255
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm255, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
