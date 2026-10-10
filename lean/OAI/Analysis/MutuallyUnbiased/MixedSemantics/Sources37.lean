import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical153
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical156
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1184 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1184 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1184 : Charge := ![2, 0, 0, 1, 1, -4]
def sourceForm1184 : Integer.Sparse Master := [(Sum.inr 791, 1), (Sum.inr 1199, 2), (Sum.inr 1231, 2), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

theorem sourceEq1184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1184 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1184 + difference 0 5) (sourceB1184 + difference 5 0) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1184 + difference 0 5) (sourceB1184 + difference 5 0) sourceC1184) = raw19855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19855; decide +kernel
    rw [ha]
    exact (canonical19855 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1184 + difference 1 5) (sourceB1184 + difference 5 1) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1199) := by
    have ha : (tripleCharges (sourceA1184 + difference 1 5) (sourceB1184 + difference 5 1) sourceC1184) = raw19861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19861; decide +kernel
    rw [ha]
    exact (canonical19861 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1184 + difference 2 5) (sourceB1184 + difference 5 2) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1199) := by
    have ha : (tripleCharges (sourceA1184 + difference 2 5) (sourceB1184 + difference 5 2) sourceC1184) = raw19862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19862; decide +kernel
    rw [ha]
    exact (canonical19862 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1184 + difference 3 5) (sourceB1184 + difference 5 3) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1231) := by
    have ha : (tripleCharges (sourceA1184 + difference 3 5) (sourceB1184 + difference 5 3) sourceC1184) = raw19863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19863; decide +kernel
    rw [ha]
    exact (canonical19863 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1184 + difference 4 5) (sourceB1184 + difference 5 4) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1231) := by
    have ha : (tripleCharges (sourceA1184 + difference 4 5) (sourceB1184 + difference 5 4) sourceC1184) = raw19864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19864; decide +kernel
    rw [ha]
    exact (canonical19864 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1184 + difference 5 5) (sourceB1184 + difference 5 5) sourceC1184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 791) := by
    have ha : (tripleCharges (sourceA1184 + difference 5 5) (sourceB1184 + difference 5 5) sourceC1184) = raw19850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1184 sourceB1184 sourceC1184 difference raw19850; decide +kernel
    rw [ha]
    exact (canonical19850 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1184 + sourceB1184) sourceC1184) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1184 + sourceB1184) sourceC1184) = raw19856 := by
      apply Matrix.ext; unfold doubleCharges sourceA1184 sourceB1184 sourceC1184 raw19856; decide +kernel
    rw [ha]
    exact (canonical19856 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1184 sourceB1184 sourceC1184
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1184, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1185 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1185 : Charge := ![2, 0, 0, 1, 1, -4]
def sourceC1185 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1185 : Integer.Sparse Master := [(Sum.inr 553, 1), (Sum.inr 711, 2), (Sum.inr 849, 1), (Sum.inr 855, 2), (Sum.inr 4072, -1)]

theorem sourceEq1185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1185 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1185 + difference 0 0) (sourceB1185 + difference 0 0) sourceC1185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 849) := by
    have ha : (tripleCharges (sourceA1185 + difference 0 0) (sourceB1185 + difference 0 0) sourceC1185) = raw19865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1185 sourceB1185 sourceC1185 difference raw19865; decide +kernel
    rw [ha]
    exact (canonical19865 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1185 + difference 1 0) (sourceB1185 + difference 0 1) sourceC1185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 711) := by
    have ha : (tripleCharges (sourceA1185 + difference 1 0) (sourceB1185 + difference 0 1) sourceC1185) = raw19866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1185 sourceB1185 sourceC1185 difference raw19866; decide +kernel
    rw [ha]
    exact (canonical19866 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1185 + difference 2 0) (sourceB1185 + difference 0 2) sourceC1185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 711) := by
    have ha : (tripleCharges (sourceA1185 + difference 2 0) (sourceB1185 + difference 0 2) sourceC1185) = raw19867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1185 sourceB1185 sourceC1185 difference raw19867; decide +kernel
    rw [ha]
    exact (canonical19867 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1185 + difference 3 0) (sourceB1185 + difference 0 3) sourceC1185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 855) := by
    have ha : (tripleCharges (sourceA1185 + difference 3 0) (sourceB1185 + difference 0 3) sourceC1185) = raw19829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1185 sourceB1185 sourceC1185 difference raw19829; decide +kernel
    rw [ha]
    exact (canonical19829 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1185 + difference 4 0) (sourceB1185 + difference 0 4) sourceC1185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 855) := by
    have ha : (tripleCharges (sourceA1185 + difference 4 0) (sourceB1185 + difference 0 4) sourceC1185) = raw19868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1185 sourceB1185 sourceC1185 difference raw19868; decide +kernel
    rw [ha]
    exact (canonical19868 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1185 + difference 5 0) (sourceB1185 + difference 0 5) sourceC1185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 553) := by
    have ha : (tripleCharges (sourceA1185 + difference 5 0) (sourceB1185 + difference 0 5) sourceC1185) = raw19869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1185 sourceB1185 sourceC1185 difference raw19869; decide +kernel
    rw [ha]
    exact (canonical19869 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1185 + sourceB1185) sourceC1185) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1185 + sourceB1185) sourceC1185) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1185 sourceB1185 sourceC1185 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1185 sourceB1185 sourceC1185
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1185, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1186 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1186 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1186 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceForm1186 : Integer.Sparse Master := [(Sum.inr 979, 2), (Sum.inr 986, 1), (Sum.inr 1007, 1), (Sum.inr 1037, 1), (Sum.inr 2208, 1), (Sum.inr 4081, -1)]

theorem sourceEq1186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1186 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 0) (sourceB1186 + difference 0 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 986) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 0) (sourceB1186 + difference 0 0) sourceC1186) = raw19870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19870; decide +kernel
    rw [ha]
    exact (canonical19870 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 1) (sourceB1186 + difference 1 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 1) (sourceB1186 + difference 1 0) sourceC1186) = raw19871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19871; decide +kernel
    rw [ha]
    exact (canonical19871 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 2) (sourceB1186 + difference 2 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 2) (sourceB1186 + difference 2 0) sourceC1186) = raw19872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19872; decide +kernel
    rw [ha]
    exact (canonical19872 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 3) (sourceB1186 + difference 3 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 3) (sourceB1186 + difference 3 0) sourceC1186) = raw19873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19873; decide +kernel
    rw [ha]
    exact (canonical19873 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 4) (sourceB1186 + difference 4 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1007) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 4) (sourceB1186 + difference 4 0) sourceC1186) = raw19874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19874; decide +kernel
    rw [ha]
    exact (canonical19874 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1186 + difference 0 5) (sourceB1186 + difference 5 0) sourceC1186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1186 + difference 0 5) (sourceB1186 + difference 5 0) sourceC1186) = raw19875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1186 sourceB1186 sourceC1186 difference raw19875; decide +kernel
    rw [ha]
    exact (canonical19875 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1186 + sourceB1186) sourceC1186) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1186 + sourceB1186) sourceC1186) = raw19876 := by
      apply Matrix.ext; unfold doubleCharges sourceA1186 sourceB1186 sourceC1186 raw19876; decide +kernel
    rw [ha]
    exact (canonical19876 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1186 sourceB1186 sourceC1186
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1186, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1187 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1187 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1187 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceForm1187 : Integer.Sparse Master := [(Sum.inr 574, 1), (Sum.inr 867, 2), (Sum.inr 890, 1), (Sum.inr 986, 1), (Sum.inr 1007, 1), (Sum.inr 4081, -1)]

theorem sourceEq1187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1187 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1187 + difference 1 0) (sourceB1187 + difference 0 1) sourceC1187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 574) := by
    have ha : (tripleCharges (sourceA1187 + difference 1 0) (sourceB1187 + difference 0 1) sourceC1187) = raw19877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1187 sourceB1187 sourceC1187 difference raw19877; decide +kernel
    rw [ha]
    exact (canonical19877 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1187 + difference 1 1) (sourceB1187 + difference 1 1) sourceC1187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 986) := by
    have ha : (tripleCharges (sourceA1187 + difference 1 1) (sourceB1187 + difference 1 1) sourceC1187) = raw19870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1187 sourceB1187 sourceC1187 difference raw19870; decide +kernel
    rw [ha]
    exact (canonical19870 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1187 + difference 1 2) (sourceB1187 + difference 2 1) sourceC1187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 867) := by
    have ha : (tripleCharges (sourceA1187 + difference 1 2) (sourceB1187 + difference 2 1) sourceC1187) = raw19878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1187 sourceB1187 sourceC1187 difference raw19878; decide +kernel
    rw [ha]
    exact (canonical19878 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1187 + difference 1 3) (sourceB1187 + difference 3 1) sourceC1187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 867) := by
    have ha : (tripleCharges (sourceA1187 + difference 1 3) (sourceB1187 + difference 3 1) sourceC1187) = raw19879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1187 sourceB1187 sourceC1187 difference raw19879; decide +kernel
    rw [ha]
    exact (canonical19879 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1187 + difference 1 4) (sourceB1187 + difference 4 1) sourceC1187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 890) := by
    have ha : (tripleCharges (sourceA1187 + difference 1 4) (sourceB1187 + difference 4 1) sourceC1187) = raw19880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1187 sourceB1187 sourceC1187 difference raw19880; decide +kernel
    rw [ha]
    exact (canonical19880 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1187 + difference 1 5) (sourceB1187 + difference 5 1) sourceC1187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1007) := by
    have ha : (tripleCharges (sourceA1187 + difference 1 5) (sourceB1187 + difference 5 1) sourceC1187) = raw19881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1187 sourceB1187 sourceC1187 difference raw19881; decide +kernel
    rw [ha]
    exact (canonical19881 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1187 + sourceB1187) sourceC1187) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1187 + sourceB1187) sourceC1187) = raw19876 := by
      apply Matrix.ext; unfold doubleCharges sourceA1187 sourceB1187 sourceC1187 raw19876; decide +kernel
    rw [ha]
    exact (canonical19876 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1187 sourceB1187 sourceC1187
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1187, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1188 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1188 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceC1188 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1188 : Integer.Sparse Master := [(Sum.inr 711, 2), (Sum.inr 718, 1), (Sum.inr 727, 1), (Sum.inr 855, 1), (Sum.inr 1620, 1), (Sum.inr 4072, -1)]

theorem sourceEq1188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1188 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1188 + difference 0 0) (sourceB1188 + difference 0 0) sourceC1188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1620) := by
    have ha : (tripleCharges (sourceA1188 + difference 0 0) (sourceB1188 + difference 0 0) sourceC1188) = raw19825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1188 sourceB1188 sourceC1188 difference raw19825; decide +kernel
    rw [ha]
    exact (canonical19825 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1188 + difference 1 0) (sourceB1188 + difference 0 1) sourceC1188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 727) := by
    have ha : (tripleCharges (sourceA1188 + difference 1 0) (sourceB1188 + difference 0 1) sourceC1188) = raw19882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1188 sourceB1188 sourceC1188 difference raw19882; decide +kernel
    rw [ha]
    exact (canonical19882 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1188 + difference 2 0) (sourceB1188 + difference 0 2) sourceC1188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 711) := by
    have ha : (tripleCharges (sourceA1188 + difference 2 0) (sourceB1188 + difference 0 2) sourceC1188) = raw19883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1188 sourceB1188 sourceC1188 difference raw19883; decide +kernel
    rw [ha]
    exact (canonical19883 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1188 + difference 3 0) (sourceB1188 + difference 0 3) sourceC1188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 711) := by
    have ha : (tripleCharges (sourceA1188 + difference 3 0) (sourceB1188 + difference 0 3) sourceC1188) = raw19884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1188 sourceB1188 sourceC1188 difference raw19884; decide +kernel
    rw [ha]
    exact (canonical19884 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1188 + difference 4 0) (sourceB1188 + difference 0 4) sourceC1188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 855) := by
    have ha : (tripleCharges (sourceA1188 + difference 4 0) (sourceB1188 + difference 0 4) sourceC1188) = raw19885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1188 sourceB1188 sourceC1188 difference raw19885; decide +kernel
    rw [ha]
    exact (canonical19885 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1188 + difference 5 0) (sourceB1188 + difference 0 5) sourceC1188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 718) := by
    have ha : (tripleCharges (sourceA1188 + difference 5 0) (sourceB1188 + difference 0 5) sourceC1188) = raw19886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1188 sourceB1188 sourceC1188 difference raw19886; decide +kernel
    rw [ha]
    exact (canonical19886 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1188 + sourceB1188) sourceC1188) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1188 + sourceB1188) sourceC1188) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1188 sourceB1188 sourceC1188 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1188 sourceB1188 sourceC1188
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1188, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1189 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1189 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1189 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1189 : Integer.Sparse Master := [(Sum.inr 4085, 1), (Sum.inr 4181, 8), (Sum.inr 4194, 1), (Sum.inr 4350, 12), (Sum.inr 4501, 8)]

theorem sourceEq1189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1189 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1189 + difference 0 1) (sourceB1189 + difference 1 0) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1189 + difference 0 1) (sourceB1189 + difference 1 0) sourceC1189) = raw19887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19887; decide +kernel
    rw [ha]
    exact (canonical19887 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1189 + difference 0 2) (sourceB1189 + difference 2 0) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1189 + difference 0 2) (sourceB1189 + difference 2 0) sourceC1189) = raw19888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19888; decide +kernel
    rw [ha]
    exact (canonical19888 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1189 + difference 0 3) (sourceB1189 + difference 3 0) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1189 + difference 0 3) (sourceB1189 + difference 3 0) sourceC1189) = raw19889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19889; decide +kernel
    rw [ha]
    exact (canonical19889 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1189 + difference 0 4) (sourceB1189 + difference 4 0) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1189 + difference 0 4) (sourceB1189 + difference 4 0) sourceC1189) = raw19890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19890; decide +kernel
    rw [ha]
    exact (canonical19890 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1189 + difference 0 5) (sourceB1189 + difference 5 0) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA1189 + difference 0 5) (sourceB1189 + difference 5 0) sourceC1189) = raw19891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19891; decide +kernel
    rw [ha]
    exact (canonical19891 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1189 + difference 1 0) (sourceB1189 + difference 0 1) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1189 + difference 1 0) (sourceB1189 + difference 0 1) sourceC1189) = raw19892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19892; decide +kernel
    rw [ha]
    exact (canonical19892 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1189 + difference 1 2) (sourceB1189 + difference 2 1) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 1 2) (sourceB1189 + difference 2 1) sourceC1189) = raw19893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19893; decide +kernel
    rw [ha]
    exact (canonical19893 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1189 + difference 1 3) (sourceB1189 + difference 3 1) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 1 3) (sourceB1189 + difference 3 1) sourceC1189) = raw19894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19894; decide +kernel
    rw [ha]
    exact (canonical19894 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1189 + difference 1 4) (sourceB1189 + difference 4 1) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 1 4) (sourceB1189 + difference 4 1) sourceC1189) = raw19895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19895; decide +kernel
    rw [ha]
    exact (canonical19895 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1189 + difference 1 5) (sourceB1189 + difference 5 1) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1189 + difference 1 5) (sourceB1189 + difference 5 1) sourceC1189) = raw19896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19896; decide +kernel
    rw [ha]
    exact (canonical19896 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1189 + difference 2 0) (sourceB1189 + difference 0 2) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1189 + difference 2 0) (sourceB1189 + difference 0 2) sourceC1189) = raw19897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19897; decide +kernel
    rw [ha]
    exact (canonical19897 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1189 + difference 2 1) (sourceB1189 + difference 1 2) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 2 1) (sourceB1189 + difference 1 2) sourceC1189) = raw19898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19898; decide +kernel
    rw [ha]
    exact (canonical19898 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1189 + difference 2 3) (sourceB1189 + difference 3 2) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 2 3) (sourceB1189 + difference 3 2) sourceC1189) = raw19899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19899; decide +kernel
    rw [ha]
    exact (canonical19899 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1189 + difference 2 4) (sourceB1189 + difference 4 2) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 2 4) (sourceB1189 + difference 4 2) sourceC1189) = raw19900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19900; decide +kernel
    rw [ha]
    exact (canonical19900 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1189 + difference 2 5) (sourceB1189 + difference 5 2) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1189 + difference 2 5) (sourceB1189 + difference 5 2) sourceC1189) = raw19901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19901; decide +kernel
    rw [ha]
    exact (canonical19901 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1189 + difference 3 0) (sourceB1189 + difference 0 3) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1189 + difference 3 0) (sourceB1189 + difference 0 3) sourceC1189) = raw19902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19902; decide +kernel
    rw [ha]
    exact (canonical19902 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1189 + difference 3 1) (sourceB1189 + difference 1 3) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 3 1) (sourceB1189 + difference 1 3) sourceC1189) = raw19903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19903; decide +kernel
    rw [ha]
    exact (canonical19903 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1189 + difference 3 2) (sourceB1189 + difference 2 3) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 3 2) (sourceB1189 + difference 2 3) sourceC1189) = raw19904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19904; decide +kernel
    rw [ha]
    exact (canonical19904 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1189 + difference 3 4) (sourceB1189 + difference 4 3) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 3 4) (sourceB1189 + difference 4 3) sourceC1189) = raw19905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19905; decide +kernel
    rw [ha]
    exact (canonical19905 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1189 + difference 3 5) (sourceB1189 + difference 5 3) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1189 + difference 3 5) (sourceB1189 + difference 5 3) sourceC1189) = raw19906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19906; decide +kernel
    rw [ha]
    exact (canonical19906 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1189 + difference 4 0) (sourceB1189 + difference 0 4) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1189 + difference 4 0) (sourceB1189 + difference 0 4) sourceC1189) = raw19907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19907; decide +kernel
    rw [ha]
    exact (canonical19907 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1189 + difference 4 1) (sourceB1189 + difference 1 4) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 4 1) (sourceB1189 + difference 1 4) sourceC1189) = raw19908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19908; decide +kernel
    rw [ha]
    exact (canonical19908 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1189 + difference 4 2) (sourceB1189 + difference 2 4) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 4 2) (sourceB1189 + difference 2 4) sourceC1189) = raw19909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19909; decide +kernel
    rw [ha]
    exact (canonical19909 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1189 + difference 4 3) (sourceB1189 + difference 3 4) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1189 + difference 4 3) (sourceB1189 + difference 3 4) sourceC1189) = raw19910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19910; decide +kernel
    rw [ha]
    exact (canonical19910 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1189 + difference 4 5) (sourceB1189 + difference 5 4) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1189 + difference 4 5) (sourceB1189 + difference 5 4) sourceC1189) = raw19911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19911; decide +kernel
    rw [ha]
    exact (canonical19911 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1189 + difference 5 0) (sourceB1189 + difference 0 5) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4194) := by
    have ha : (tripleCharges (sourceA1189 + difference 5 0) (sourceB1189 + difference 0 5) sourceC1189) = raw19912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19912; decide +kernel
    rw [ha]
    exact (canonical19912 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1189 + difference 5 1) (sourceB1189 + difference 1 5) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1189 + difference 5 1) (sourceB1189 + difference 1 5) sourceC1189) = raw19913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19913; decide +kernel
    rw [ha]
    exact (canonical19913 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1189 + difference 5 2) (sourceB1189 + difference 2 5) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1189 + difference 5 2) (sourceB1189 + difference 2 5) sourceC1189) = raw19914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19914; decide +kernel
    rw [ha]
    exact (canonical19914 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1189 + difference 5 3) (sourceB1189 + difference 3 5) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1189 + difference 5 3) (sourceB1189 + difference 3 5) sourceC1189) = raw19915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19915; decide +kernel
    rw [ha]
    exact (canonical19915 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1189 + difference 5 4) (sourceB1189 + difference 4 5) sourceC1189) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1189 + difference 5 4) (sourceB1189 + difference 4 5) sourceC1189) = raw19916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1189 sourceB1189 sourceC1189 difference raw19916; decide +kernel
    rw [ha]
    exact (canonical19916 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1189 sourceB1189 sourceC1189
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1189, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1190 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1190 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1190 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1190 : Integer.Sparse Master := [(Sum.inr 1521, 8), (Sum.inr 1541, 1), (Sum.inr 1677, 12), (Sum.inr 1730, 8), (Sum.inr 4085, 1)]

theorem sourceEq1190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1190 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1190 + difference 0 1) (sourceB1190 + difference 1 0) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 0 1) (sourceB1190 + difference 1 0) sourceC1190) = raw19917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19917; decide +kernel
    rw [ha]
    exact (canonical19917 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1190 + difference 0 2) (sourceB1190 + difference 2 0) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 0 2) (sourceB1190 + difference 2 0) sourceC1190) = raw19918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19918; decide +kernel
    rw [ha]
    exact (canonical19918 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1190 + difference 0 3) (sourceB1190 + difference 3 0) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 0 3) (sourceB1190 + difference 3 0) sourceC1190) = raw19919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19919; decide +kernel
    rw [ha]
    exact (canonical19919 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1190 + difference 0 4) (sourceB1190 + difference 4 0) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 0 4) (sourceB1190 + difference 4 0) sourceC1190) = raw19920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19920; decide +kernel
    rw [ha]
    exact (canonical19920 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1190 + difference 0 5) (sourceB1190 + difference 5 0) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA1190 + difference 0 5) (sourceB1190 + difference 5 0) sourceC1190) = raw19921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19921; decide +kernel
    rw [ha]
    exact (canonical19921 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1190 + difference 1 0) (sourceB1190 + difference 0 1) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 1 0) (sourceB1190 + difference 0 1) sourceC1190) = raw19922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19922; decide +kernel
    rw [ha]
    exact (canonical19922 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1190 + difference 1 2) (sourceB1190 + difference 2 1) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 1 2) (sourceB1190 + difference 2 1) sourceC1190) = raw19923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19923; decide +kernel
    rw [ha]
    exact (canonical19923 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1190 + difference 1 3) (sourceB1190 + difference 3 1) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 1 3) (sourceB1190 + difference 3 1) sourceC1190) = raw19924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19924; decide +kernel
    rw [ha]
    exact (canonical19924 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1190 + difference 1 4) (sourceB1190 + difference 4 1) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 1 4) (sourceB1190 + difference 4 1) sourceC1190) = raw19925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19925; decide +kernel
    rw [ha]
    exact (canonical19925 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1190 + difference 1 5) (sourceB1190 + difference 5 1) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 1 5) (sourceB1190 + difference 5 1) sourceC1190) = raw19926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19926; decide +kernel
    rw [ha]
    exact (canonical19926 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1190 + difference 2 0) (sourceB1190 + difference 0 2) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 2 0) (sourceB1190 + difference 0 2) sourceC1190) = raw19927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19927; decide +kernel
    rw [ha]
    exact (canonical19927 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1190 + difference 2 1) (sourceB1190 + difference 1 2) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 2 1) (sourceB1190 + difference 1 2) sourceC1190) = raw19928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19928; decide +kernel
    rw [ha]
    exact (canonical19928 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1190 + difference 2 3) (sourceB1190 + difference 3 2) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 2 3) (sourceB1190 + difference 3 2) sourceC1190) = raw19929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19929; decide +kernel
    rw [ha]
    exact (canonical19929 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1190 + difference 2 4) (sourceB1190 + difference 4 2) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 2 4) (sourceB1190 + difference 4 2) sourceC1190) = raw19930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19930; decide +kernel
    rw [ha]
    exact (canonical19930 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1190 + difference 2 5) (sourceB1190 + difference 5 2) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 2 5) (sourceB1190 + difference 5 2) sourceC1190) = raw19931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19931; decide +kernel
    rw [ha]
    exact (canonical19931 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1190 + difference 3 0) (sourceB1190 + difference 0 3) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 3 0) (sourceB1190 + difference 0 3) sourceC1190) = raw19932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19932; decide +kernel
    rw [ha]
    exact (canonical19932 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1190 + difference 3 1) (sourceB1190 + difference 1 3) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 3 1) (sourceB1190 + difference 1 3) sourceC1190) = raw19933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19933; decide +kernel
    rw [ha]
    exact (canonical19933 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1190 + difference 3 2) (sourceB1190 + difference 2 3) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 3 2) (sourceB1190 + difference 2 3) sourceC1190) = raw19934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19934; decide +kernel
    rw [ha]
    exact (canonical19934 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1190 + difference 3 4) (sourceB1190 + difference 4 3) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 3 4) (sourceB1190 + difference 4 3) sourceC1190) = raw19935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19935; decide +kernel
    rw [ha]
    exact (canonical19935 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1190 + difference 3 5) (sourceB1190 + difference 5 3) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 3 5) (sourceB1190 + difference 5 3) sourceC1190) = raw19936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19936; decide +kernel
    rw [ha]
    exact (canonical19936 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1190 + difference 4 0) (sourceB1190 + difference 0 4) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 4 0) (sourceB1190 + difference 0 4) sourceC1190) = raw19937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19937; decide +kernel
    rw [ha]
    exact (canonical19937 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1190 + difference 4 1) (sourceB1190 + difference 1 4) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 4 1) (sourceB1190 + difference 1 4) sourceC1190) = raw19938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19938; decide +kernel
    rw [ha]
    exact (canonical19938 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1190 + difference 4 2) (sourceB1190 + difference 2 4) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 4 2) (sourceB1190 + difference 2 4) sourceC1190) = raw19939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19939; decide +kernel
    rw [ha]
    exact (canonical19939 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1190 + difference 4 3) (sourceB1190 + difference 3 4) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1190 + difference 4 3) (sourceB1190 + difference 3 4) sourceC1190) = raw19940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19940; decide +kernel
    rw [ha]
    exact (canonical19940 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1190 + difference 4 5) (sourceB1190 + difference 5 4) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1190 + difference 4 5) (sourceB1190 + difference 5 4) sourceC1190) = raw19941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19941; decide +kernel
    rw [ha]
    exact (canonical19941 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1190 + difference 5 0) (sourceB1190 + difference 0 5) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1541) := by
    have ha : (tripleCharges (sourceA1190 + difference 5 0) (sourceB1190 + difference 0 5) sourceC1190) = raw19942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19942; decide +kernel
    rw [ha]
    exact (canonical19942 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1190 + difference 5 1) (sourceB1190 + difference 1 5) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 5 1) (sourceB1190 + difference 1 5) sourceC1190) = raw19943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19943; decide +kernel
    rw [ha]
    exact (canonical19943 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1190 + difference 5 2) (sourceB1190 + difference 2 5) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 5 2) (sourceB1190 + difference 2 5) sourceC1190) = raw19944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19944; decide +kernel
    rw [ha]
    exact (canonical19944 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1190 + difference 5 3) (sourceB1190 + difference 3 5) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 5 3) (sourceB1190 + difference 3 5) sourceC1190) = raw19945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19945; decide +kernel
    rw [ha]
    exact (canonical19945 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1190 + difference 5 4) (sourceB1190 + difference 4 5) sourceC1190) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1190 + difference 5 4) (sourceB1190 + difference 4 5) sourceC1190) = raw19946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1190 sourceB1190 sourceC1190 difference raw19946; decide +kernel
    rw [ha]
    exact (canonical19946 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1190 sourceB1190 sourceC1190
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1190, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1191 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1191 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1191 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1191 : Integer.Sparse Master := [(Sum.inr 609, 4), (Sum.inr 622, 1), (Sum.inr 1096, 1), (Sum.inr 4085, -1)]

theorem sourceEq1191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1191 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1191 + difference 0 0) (sourceB1191 + difference 0 0) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1096) := by
    have ha : (tripleCharges (sourceA1191 + difference 0 0) (sourceB1191 + difference 0 0) sourceC1191) = raw19947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19947; decide +kernel
    rw [ha]
    exact (canonical19947 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1191 + difference 1 0) (sourceB1191 + difference 0 1) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1191 + difference 1 0) (sourceB1191 + difference 0 1) sourceC1191) = raw19948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19948; decide +kernel
    rw [ha]
    exact (canonical19948 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1191 + difference 2 0) (sourceB1191 + difference 0 2) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1191 + difference 2 0) (sourceB1191 + difference 0 2) sourceC1191) = raw19949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19949; decide +kernel
    rw [ha]
    exact (canonical19949 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1191 + difference 3 0) (sourceB1191 + difference 0 3) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1191 + difference 3 0) (sourceB1191 + difference 0 3) sourceC1191) = raw19950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19950; decide +kernel
    rw [ha]
    exact (canonical19950 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1191 + difference 4 0) (sourceB1191 + difference 0 4) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1191 + difference 4 0) (sourceB1191 + difference 0 4) sourceC1191) = raw19951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19951; decide +kernel
    rw [ha]
    exact (canonical19951 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1191 + difference 5 0) (sourceB1191 + difference 0 5) sourceC1191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 622) := by
    have ha : (tripleCharges (sourceA1191 + difference 5 0) (sourceB1191 + difference 0 5) sourceC1191) = raw19952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1191 sourceB1191 sourceC1191 difference raw19952; decide +kernel
    rw [ha]
    exact (canonical19952 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1191 + sourceB1191) sourceC1191) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1191 + sourceB1191) sourceC1191) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA1191 sourceB1191 sourceC1191 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1191 sourceB1191 sourceC1191
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1191, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1192 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceB1192 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1192 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1192 : Integer.Sparse Master := [(Sum.inr 4072, 1), (Sum.inr 4274, 8), (Sum.inr 4405, 12), (Sum.inr 4468, 8), (Sum.inr 4629, 1)]

theorem sourceEq1192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1192 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1192 + difference 0 1) (sourceB1192 + difference 1 0) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1192 + difference 0 1) (sourceB1192 + difference 1 0) sourceC1192) = raw19581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19581; decide +kernel
    rw [ha]
    exact (canonical19581 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1192 + difference 0 2) (sourceB1192 + difference 2 0) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1192 + difference 0 2) (sourceB1192 + difference 2 0) sourceC1192) = raw19582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19582; decide +kernel
    rw [ha]
    exact (canonical19582 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1192 + difference 0 3) (sourceB1192 + difference 3 0) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1192 + difference 0 3) (sourceB1192 + difference 3 0) sourceC1192) = raw19583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19583; decide +kernel
    rw [ha]
    exact (canonical19583 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1192 + difference 0 4) (sourceB1192 + difference 4 0) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1192 + difference 0 4) (sourceB1192 + difference 4 0) sourceC1192) = raw19584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19584; decide +kernel
    rw [ha]
    exact (canonical19584 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1192 + difference 0 5) (sourceB1192 + difference 5 0) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4629) := by
    have ha : (tripleCharges (sourceA1192 + difference 0 5) (sourceB1192 + difference 5 0) sourceC1192) = raw19766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19766; decide +kernel
    rw [ha]
    exact (canonical19766 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1192 + difference 1 0) (sourceB1192 + difference 0 1) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1192 + difference 1 0) (sourceB1192 + difference 0 1) sourceC1192) = raw19954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19954; decide +kernel
    rw [ha]
    exact (canonical19954 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1192 + difference 1 2) (sourceB1192 + difference 2 1) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 1 2) (sourceB1192 + difference 2 1) sourceC1192) = raw19955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19955; decide +kernel
    rw [ha]
    exact (canonical19955 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1192 + difference 1 3) (sourceB1192 + difference 3 1) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 1 3) (sourceB1192 + difference 3 1) sourceC1192) = raw19956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19956; decide +kernel
    rw [ha]
    exact (canonical19956 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1192 + difference 1 4) (sourceB1192 + difference 4 1) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 1 4) (sourceB1192 + difference 4 1) sourceC1192) = raw19754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19754; decide +kernel
    rw [ha]
    exact (canonical19754 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1192 + difference 1 5) (sourceB1192 + difference 5 1) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1192 + difference 1 5) (sourceB1192 + difference 5 1) sourceC1192) = raw19560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19560; decide +kernel
    rw [ha]
    exact (canonical19560 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1192 + difference 2 0) (sourceB1192 + difference 0 2) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1192 + difference 2 0) (sourceB1192 + difference 0 2) sourceC1192) = raw19957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19957; decide +kernel
    rw [ha]
    exact (canonical19957 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1192 + difference 2 1) (sourceB1192 + difference 1 2) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 2 1) (sourceB1192 + difference 1 2) sourceC1192) = raw19958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19958; decide +kernel
    rw [ha]
    exact (canonical19958 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1192 + difference 2 3) (sourceB1192 + difference 3 2) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 2 3) (sourceB1192 + difference 3 2) sourceC1192) = raw19959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19959; decide +kernel
    rw [ha]
    exact (canonical19959 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1192 + difference 2 4) (sourceB1192 + difference 4 2) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 2 4) (sourceB1192 + difference 4 2) sourceC1192) = raw19758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19758; decide +kernel
    rw [ha]
    exact (canonical19758 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1192 + difference 2 5) (sourceB1192 + difference 5 2) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1192 + difference 2 5) (sourceB1192 + difference 5 2) sourceC1192) = raw19565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19565; decide +kernel
    rw [ha]
    exact (canonical19565 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1192 + difference 3 0) (sourceB1192 + difference 0 3) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1192 + difference 3 0) (sourceB1192 + difference 0 3) sourceC1192) = raw19960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19960; decide +kernel
    rw [ha]
    exact (canonical19960 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1192 + difference 3 1) (sourceB1192 + difference 1 3) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 3 1) (sourceB1192 + difference 1 3) sourceC1192) = raw19961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19961; decide +kernel
    rw [ha]
    exact (canonical19961 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1192 + difference 3 2) (sourceB1192 + difference 2 3) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 3 2) (sourceB1192 + difference 2 3) sourceC1192) = raw19962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19962; decide +kernel
    rw [ha]
    exact (canonical19962 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1192 + difference 3 4) (sourceB1192 + difference 4 3) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 3 4) (sourceB1192 + difference 4 3) sourceC1192) = raw19762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19762; decide +kernel
    rw [ha]
    exact (canonical19762 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1192 + difference 3 5) (sourceB1192 + difference 5 3) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1192 + difference 3 5) (sourceB1192 + difference 5 3) sourceC1192) = raw19570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19570; decide +kernel
    rw [ha]
    exact (canonical19570 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1192 + difference 4 0) (sourceB1192 + difference 0 4) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1192 + difference 4 0) (sourceB1192 + difference 0 4) sourceC1192) = raw19963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19963; decide +kernel
    rw [ha]
    exact (canonical19963 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1192 + difference 4 1) (sourceB1192 + difference 1 4) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 4 1) (sourceB1192 + difference 1 4) sourceC1192) = raw19964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19964; decide +kernel
    rw [ha]
    exact (canonical19964 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1192 + difference 4 2) (sourceB1192 + difference 2 4) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 4 2) (sourceB1192 + difference 2 4) sourceC1192) = raw19965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19965; decide +kernel
    rw [ha]
    exact (canonical19965 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1192 + difference 4 3) (sourceB1192 + difference 3 4) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1192 + difference 4 3) (sourceB1192 + difference 3 4) sourceC1192) = raw19966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19966; decide +kernel
    rw [ha]
    exact (canonical19966 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1192 + difference 4 5) (sourceB1192 + difference 5 4) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1192 + difference 4 5) (sourceB1192 + difference 5 4) sourceC1192) = raw19575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19575; decide +kernel
    rw [ha]
    exact (canonical19575 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1192 + difference 5 0) (sourceB1192 + difference 0 5) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (tripleCharges (sourceA1192 + difference 5 0) (sourceB1192 + difference 0 5) sourceC1192) = raw19967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19967; decide +kernel
    rw [ha]
    exact (canonical19967 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1192 + difference 5 1) (sourceB1192 + difference 1 5) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1192 + difference 5 1) (sourceB1192 + difference 1 5) sourceC1192) = raw19968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19968; decide +kernel
    rw [ha]
    exact (canonical19968 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1192 + difference 5 2) (sourceB1192 + difference 2 5) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1192 + difference 5 2) (sourceB1192 + difference 2 5) sourceC1192) = raw19969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19969; decide +kernel
    rw [ha]
    exact (canonical19969 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1192 + difference 5 3) (sourceB1192 + difference 3 5) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1192 + difference 5 3) (sourceB1192 + difference 3 5) sourceC1192) = raw19970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19970; decide +kernel
    rw [ha]
    exact (canonical19970 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1192 + difference 5 4) (sourceB1192 + difference 4 5) sourceC1192) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1192 + difference 5 4) (sourceB1192 + difference 4 5) sourceC1192) = raw19767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1192 sourceB1192 sourceC1192 difference raw19767; decide +kernel
    rw [ha]
    exact (canonical19767 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1192 sourceB1192 sourceC1192
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1192, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1193 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1193 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1193 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceForm1193 : Integer.Sparse Master := [(Sum.inr 4070, 1), (Sum.inr 4103, 3), (Sum.inr 4112, 1), (Sum.inr 4131, 1), (Sum.inr 4142, 3), (Sum.inr 4168, 1), (Sum.inr 4198, 6), (Sum.inr 4222, 3), (Sum.inr 4235, 3), (Sum.inr 4266, 3), (Sum.inr 4421, 3), (Sum.inr 4493, 1), (Sum.inr 4501, 1)]

theorem sourceEq1193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1193 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1193 + difference 0 1) (sourceB1193 + difference 1 0) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4266) := by
    have ha : (tripleCharges (sourceA1193 + difference 0 1) (sourceB1193 + difference 1 0) sourceC1193) = raw19971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19971; decide +kernel
    rw [ha]
    exact (canonical19971 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1193 + difference 0 2) (sourceB1193 + difference 2 0) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4266) := by
    have ha : (tripleCharges (sourceA1193 + difference 0 2) (sourceB1193 + difference 2 0) sourceC1193) = raw19972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19972; decide +kernel
    rw [ha]
    exact (canonical19972 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1193 + difference 0 3) (sourceB1193 + difference 3 0) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4266) := by
    have ha : (tripleCharges (sourceA1193 + difference 0 3) (sourceB1193 + difference 3 0) sourceC1193) = raw19973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19973; decide +kernel
    rw [ha]
    exact (canonical19973 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1193 + difference 0 4) (sourceB1193 + difference 4 0) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1193 + difference 0 4) (sourceB1193 + difference 4 0) sourceC1193) = raw19974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19974; decide +kernel
    rw [ha]
    exact (canonical19974 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1193 + difference 0 5) (sourceB1193 + difference 5 0) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1193 + difference 0 5) (sourceB1193 + difference 5 0) sourceC1193) = raw19975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19975; decide +kernel
    rw [ha]
    exact (canonical19975 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1193 + difference 1 0) (sourceB1193 + difference 0 1) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4142) := by
    have ha : (tripleCharges (sourceA1193 + difference 1 0) (sourceB1193 + difference 0 1) sourceC1193) = raw19976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19976; decide +kernel
    rw [ha]
    exact (canonical19976 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1193 + difference 1 2) (sourceB1193 + difference 2 1) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA1193 + difference 1 2) (sourceB1193 + difference 2 1) sourceC1193) = raw19977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19977; decide +kernel
    rw [ha]
    exact (canonical19977 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1193 + difference 1 3) (sourceB1193 + difference 3 1) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA1193 + difference 1 3) (sourceB1193 + difference 3 1) sourceC1193) = raw19978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19978; decide +kernel
    rw [ha]
    exact (canonical19978 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1193 + difference 1 4) (sourceB1193 + difference 4 1) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4222) := by
    have ha : (tripleCharges (sourceA1193 + difference 1 4) (sourceB1193 + difference 4 1) sourceC1193) = raw19979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19979; decide +kernel
    rw [ha]
    exact (canonical19979 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1193 + difference 1 5) (sourceB1193 + difference 5 1) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4421) := by
    have ha : (tripleCharges (sourceA1193 + difference 1 5) (sourceB1193 + difference 5 1) sourceC1193) = raw19980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19980; decide +kernel
    rw [ha]
    exact (canonical19980 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1193 + difference 2 0) (sourceB1193 + difference 0 2) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4142) := by
    have ha : (tripleCharges (sourceA1193 + difference 2 0) (sourceB1193 + difference 0 2) sourceC1193) = raw19981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19981; decide +kernel
    rw [ha]
    exact (canonical19981 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1193 + difference 2 1) (sourceB1193 + difference 1 2) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA1193 + difference 2 1) (sourceB1193 + difference 1 2) sourceC1193) = raw19982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19982; decide +kernel
    rw [ha]
    exact (canonical19982 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1193 + difference 2 3) (sourceB1193 + difference 3 2) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA1193 + difference 2 3) (sourceB1193 + difference 3 2) sourceC1193) = raw19983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19983; decide +kernel
    rw [ha]
    exact (canonical19983 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1193 + difference 2 4) (sourceB1193 + difference 4 2) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4222) := by
    have ha : (tripleCharges (sourceA1193 + difference 2 4) (sourceB1193 + difference 4 2) sourceC1193) = raw19984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19984; decide +kernel
    rw [ha]
    exact (canonical19984 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1193 + difference 2 5) (sourceB1193 + difference 5 2) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4421) := by
    have ha : (tripleCharges (sourceA1193 + difference 2 5) (sourceB1193 + difference 5 2) sourceC1193) = raw19985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19985; decide +kernel
    rw [ha]
    exact (canonical19985 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1193 + difference 3 0) (sourceB1193 + difference 0 3) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4142) := by
    have ha : (tripleCharges (sourceA1193 + difference 3 0) (sourceB1193 + difference 0 3) sourceC1193) = raw19986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19986; decide +kernel
    rw [ha]
    exact (canonical19986 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1193 + difference 3 1) (sourceB1193 + difference 1 3) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA1193 + difference 3 1) (sourceB1193 + difference 1 3) sourceC1193) = raw19987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19987; decide +kernel
    rw [ha]
    exact (canonical19987 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1193 + difference 3 2) (sourceB1193 + difference 2 3) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA1193 + difference 3 2) (sourceB1193 + difference 2 3) sourceC1193) = raw19988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19988; decide +kernel
    rw [ha]
    exact (canonical19988 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1193 + difference 3 4) (sourceB1193 + difference 4 3) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4222) := by
    have ha : (tripleCharges (sourceA1193 + difference 3 4) (sourceB1193 + difference 4 3) sourceC1193) = raw19989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19989; decide +kernel
    rw [ha]
    exact (canonical19989 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1193 + difference 3 5) (sourceB1193 + difference 5 3) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4421) := by
    have ha : (tripleCharges (sourceA1193 + difference 3 5) (sourceB1193 + difference 5 3) sourceC1193) = raw19990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19990; decide +kernel
    rw [ha]
    exact (canonical19990 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1193 + difference 4 0) (sourceB1193 + difference 0 4) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4168) := by
    have ha : (tripleCharges (sourceA1193 + difference 4 0) (sourceB1193 + difference 0 4) sourceC1193) = raw19991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19991; decide +kernel
    rw [ha]
    exact (canonical19991 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1193 + difference 4 1) (sourceB1193 + difference 1 4) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4235) := by
    have ha : (tripleCharges (sourceA1193 + difference 4 1) (sourceB1193 + difference 1 4) sourceC1193) = raw19992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19992; decide +kernel
    rw [ha]
    exact (canonical19992 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1193 + difference 4 2) (sourceB1193 + difference 2 4) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4235) := by
    have ha : (tripleCharges (sourceA1193 + difference 4 2) (sourceB1193 + difference 2 4) sourceC1193) = raw19993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19993; decide +kernel
    rw [ha]
    exact (canonical19993 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1193 + difference 4 3) (sourceB1193 + difference 3 4) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4235) := by
    have ha : (tripleCharges (sourceA1193 + difference 4 3) (sourceB1193 + difference 3 4) sourceC1193) = raw19994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19994; decide +kernel
    rw [ha]
    exact (canonical19994 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1193 + difference 4 5) (sourceB1193 + difference 5 4) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4493) := by
    have ha : (tripleCharges (sourceA1193 + difference 4 5) (sourceB1193 + difference 5 4) sourceC1193) = raw19995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19995; decide +kernel
    rw [ha]
    exact (canonical19995 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1193 + difference 5 0) (sourceB1193 + difference 0 5) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4112) := by
    have ha : (tripleCharges (sourceA1193 + difference 5 0) (sourceB1193 + difference 0 5) sourceC1193) = raw19996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19996; decide +kernel
    rw [ha]
    exact (canonical19996 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1193 + difference 5 1) (sourceB1193 + difference 1 5) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4103) := by
    have ha : (tripleCharges (sourceA1193 + difference 5 1) (sourceB1193 + difference 1 5) sourceC1193) = raw19997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19997; decide +kernel
    rw [ha]
    exact (canonical19997 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1193 + difference 5 2) (sourceB1193 + difference 2 5) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4103) := by
    have ha : (tripleCharges (sourceA1193 + difference 5 2) (sourceB1193 + difference 2 5) sourceC1193) = raw19998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19998; decide +kernel
    rw [ha]
    exact (canonical19998 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1193 + difference 5 3) (sourceB1193 + difference 3 5) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4103) := by
    have ha : (tripleCharges (sourceA1193 + difference 5 3) (sourceB1193 + difference 3 5) sourceC1193) = raw19999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw19999; decide +kernel
    rw [ha]
    exact (canonical19999 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1193 + difference 5 4) (sourceB1193 + difference 4 5) sourceC1193) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4131) := by
    have ha : (tripleCharges (sourceA1193 + difference 5 4) (sourceB1193 + difference 4 5) sourceC1193) = raw20000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1193 sourceB1193 sourceC1193 difference raw20000; decide +kernel
    rw [ha]
    exact (canonical20000 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1193 sourceB1193 sourceC1193
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1193, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1194 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1194 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1194 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceForm1194 : Integer.Sparse Master := [(Sum.inr 665, 3), (Sum.inr 686, 1), (Sum.inr 691, 1), (Sum.inr 750, 6), (Sum.inr 765, 3), (Sum.inr 770, 3), (Sum.inr 801, 3), (Sum.inr 809, 3), (Sum.inr 845, 1), (Sum.inr 1002, 3), (Sum.inr 1077, 1), (Sum.inr 1085, 1), (Sum.inr 4070, 1)]

theorem sourceEq1194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1194 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1194 + difference 0 1) (sourceB1194 + difference 1 0) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1194 + difference 0 1) (sourceB1194 + difference 1 0) sourceC1194) = raw20001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20001; decide +kernel
    rw [ha]
    exact (canonical20001 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1194 + difference 0 2) (sourceB1194 + difference 2 0) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1194 + difference 0 2) (sourceB1194 + difference 2 0) sourceC1194) = raw20002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20002; decide +kernel
    rw [ha]
    exact (canonical20002 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1194 + difference 0 3) (sourceB1194 + difference 3 0) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1194 + difference 0 3) (sourceB1194 + difference 3 0) sourceC1194) = raw20003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20003; decide +kernel
    rw [ha]
    exact (canonical20003 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1194 + difference 0 4) (sourceB1194 + difference 4 0) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1194 + difference 0 4) (sourceB1194 + difference 4 0) sourceC1194) = raw20004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20004; decide +kernel
    rw [ha]
    exact (canonical20004 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1194 + difference 0 5) (sourceB1194 + difference 5 0) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1085) := by
    have ha : (tripleCharges (sourceA1194 + difference 0 5) (sourceB1194 + difference 5 0) sourceC1194) = raw20005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20005; decide +kernel
    rw [ha]
    exact (canonical20005 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1194 + difference 1 0) (sourceB1194 + difference 0 1) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 765) := by
    have ha : (tripleCharges (sourceA1194 + difference 1 0) (sourceB1194 + difference 0 1) sourceC1194) = raw20006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20006; decide +kernel
    rw [ha]
    exact (canonical20006 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1194 + difference 1 2) (sourceB1194 + difference 2 1) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 1 2) (sourceB1194 + difference 2 1) sourceC1194) = raw20007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20007; decide +kernel
    rw [ha]
    exact (canonical20007 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1194 + difference 1 3) (sourceB1194 + difference 3 1) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 1 3) (sourceB1194 + difference 3 1) sourceC1194) = raw20008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20008; decide +kernel
    rw [ha]
    exact (canonical20008 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1194 + difference 1 4) (sourceB1194 + difference 4 1) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 770) := by
    have ha : (tripleCharges (sourceA1194 + difference 1 4) (sourceB1194 + difference 4 1) sourceC1194) = raw20009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20009; decide +kernel
    rw [ha]
    exact (canonical20009 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1194 + difference 1 5) (sourceB1194 + difference 5 1) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1002) := by
    have ha : (tripleCharges (sourceA1194 + difference 1 5) (sourceB1194 + difference 5 1) sourceC1194) = raw20010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20010; decide +kernel
    rw [ha]
    exact (canonical20010 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1194 + difference 2 0) (sourceB1194 + difference 0 2) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 765) := by
    have ha : (tripleCharges (sourceA1194 + difference 2 0) (sourceB1194 + difference 0 2) sourceC1194) = raw20011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20011; decide +kernel
    rw [ha]
    exact (canonical20011 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1194 + difference 2 1) (sourceB1194 + difference 1 2) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 2 1) (sourceB1194 + difference 1 2) sourceC1194) = raw20012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20012; decide +kernel
    rw [ha]
    exact (canonical20012 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1194 + difference 2 3) (sourceB1194 + difference 3 2) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 2 3) (sourceB1194 + difference 3 2) sourceC1194) = raw20013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20013; decide +kernel
    rw [ha]
    exact (canonical20013 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1194 + difference 2 4) (sourceB1194 + difference 4 2) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 770) := by
    have ha : (tripleCharges (sourceA1194 + difference 2 4) (sourceB1194 + difference 4 2) sourceC1194) = raw20014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20014; decide +kernel
    rw [ha]
    exact (canonical20014 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1194 + difference 2 5) (sourceB1194 + difference 5 2) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1002) := by
    have ha : (tripleCharges (sourceA1194 + difference 2 5) (sourceB1194 + difference 5 2) sourceC1194) = raw20015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20015; decide +kernel
    rw [ha]
    exact (canonical20015 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1194 + difference 3 0) (sourceB1194 + difference 0 3) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 765) := by
    have ha : (tripleCharges (sourceA1194 + difference 3 0) (sourceB1194 + difference 0 3) sourceC1194) = raw20016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20016; decide +kernel
    rw [ha]
    exact (canonical20016 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1194 + difference 3 1) (sourceB1194 + difference 1 3) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 3 1) (sourceB1194 + difference 1 3) sourceC1194) = raw20017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20017; decide +kernel
    rw [ha]
    exact (canonical20017 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1194 + difference 3 2) (sourceB1194 + difference 2 3) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 750) := by
    have ha : (tripleCharges (sourceA1194 + difference 3 2) (sourceB1194 + difference 2 3) sourceC1194) = raw20018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20018; decide +kernel
    rw [ha]
    exact (canonical20018 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1194 + difference 3 4) (sourceB1194 + difference 4 3) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 770) := by
    have ha : (tripleCharges (sourceA1194 + difference 3 4) (sourceB1194 + difference 4 3) sourceC1194) = raw20019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20019; decide +kernel
    rw [ha]
    exact (canonical20019 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1194 + difference 3 5) (sourceB1194 + difference 5 3) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1002) := by
    have ha : (tripleCharges (sourceA1194 + difference 3 5) (sourceB1194 + difference 5 3) sourceC1194) = raw20020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20020; decide +kernel
    rw [ha]
    exact (canonical20020 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1194 + difference 4 0) (sourceB1194 + difference 0 4) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 845) := by
    have ha : (tripleCharges (sourceA1194 + difference 4 0) (sourceB1194 + difference 0 4) sourceC1194) = raw20021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20021; decide +kernel
    rw [ha]
    exact (canonical20021 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1194 + difference 4 1) (sourceB1194 + difference 1 4) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 801) := by
    have ha : (tripleCharges (sourceA1194 + difference 4 1) (sourceB1194 + difference 1 4) sourceC1194) = raw20022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20022; decide +kernel
    rw [ha]
    exact (canonical20022 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1194 + difference 4 2) (sourceB1194 + difference 2 4) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 801) := by
    have ha : (tripleCharges (sourceA1194 + difference 4 2) (sourceB1194 + difference 2 4) sourceC1194) = raw20023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20023; decide +kernel
    rw [ha]
    exact (canonical20023 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1194 + difference 4 3) (sourceB1194 + difference 3 4) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 801) := by
    have ha : (tripleCharges (sourceA1194 + difference 4 3) (sourceB1194 + difference 3 4) sourceC1194) = raw20024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20024; decide +kernel
    rw [ha]
    exact (canonical20024 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1194 + difference 4 5) (sourceB1194 + difference 5 4) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1077) := by
    have ha : (tripleCharges (sourceA1194 + difference 4 5) (sourceB1194 + difference 5 4) sourceC1194) = raw20025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20025; decide +kernel
    rw [ha]
    exact (canonical20025 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1194 + difference 5 0) (sourceB1194 + difference 0 5) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 686) := by
    have ha : (tripleCharges (sourceA1194 + difference 5 0) (sourceB1194 + difference 0 5) sourceC1194) = raw20026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20026; decide +kernel
    rw [ha]
    exact (canonical20026 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1194 + difference 5 1) (sourceB1194 + difference 1 5) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 665) := by
    have ha : (tripleCharges (sourceA1194 + difference 5 1) (sourceB1194 + difference 1 5) sourceC1194) = raw20027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20027; decide +kernel
    rw [ha]
    exact (canonical20027 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1194 + difference 5 2) (sourceB1194 + difference 2 5) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 665) := by
    have ha : (tripleCharges (sourceA1194 + difference 5 2) (sourceB1194 + difference 2 5) sourceC1194) = raw20028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20028; decide +kernel
    rw [ha]
    exact (canonical20028 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1194 + difference 5 3) (sourceB1194 + difference 3 5) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 665) := by
    have ha : (tripleCharges (sourceA1194 + difference 5 3) (sourceB1194 + difference 3 5) sourceC1194) = raw20029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20029; decide +kernel
    rw [ha]
    exact (canonical20029 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1194 + difference 5 4) (sourceB1194 + difference 4 5) sourceC1194) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 691) := by
    have ha : (tripleCharges (sourceA1194 + difference 5 4) (sourceB1194 + difference 4 5) sourceC1194) = raw20030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1194 sourceB1194 sourceC1194 difference raw20030; decide +kernel
    rw [ha]
    exact (canonical20030 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1194 sourceB1194 sourceC1194
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1194, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1195 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1195 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1195 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceForm1195 : Integer.Sparse Master := [(Sum.inr 549, 1), (Sum.inr 570, 3), (Sum.inr 596, 1), (Sum.inr 817, 1), (Sum.inr 4070, -1)]

theorem sourceEq1195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1195 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1195 + difference 0 0) (sourceB1195 + difference 0 0) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 817) := by
    have ha : (tripleCharges (sourceA1195 + difference 0 0) (sourceB1195 + difference 0 0) sourceC1195) = raw20031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20031; decide +kernel
    rw [ha]
    exact (canonical20031 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1195 + difference 1 0) (sourceB1195 + difference 0 1) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 570) := by
    have ha : (tripleCharges (sourceA1195 + difference 1 0) (sourceB1195 + difference 0 1) sourceC1195) = raw20032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20032; decide +kernel
    rw [ha]
    exact (canonical20032 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1195 + difference 2 0) (sourceB1195 + difference 0 2) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 570) := by
    have ha : (tripleCharges (sourceA1195 + difference 2 0) (sourceB1195 + difference 0 2) sourceC1195) = raw20033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20033; decide +kernel
    rw [ha]
    exact (canonical20033 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1195 + difference 3 0) (sourceB1195 + difference 0 3) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 570) := by
    have ha : (tripleCharges (sourceA1195 + difference 3 0) (sourceB1195 + difference 0 3) sourceC1195) = raw20034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20034; decide +kernel
    rw [ha]
    exact (canonical20034 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1195 + difference 4 0) (sourceB1195 + difference 0 4) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 596) := by
    have ha : (tripleCharges (sourceA1195 + difference 4 0) (sourceB1195 + difference 0 4) sourceC1195) = raw20035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20035; decide +kernel
    rw [ha]
    exact (canonical20035 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1195 + difference 5 0) (sourceB1195 + difference 0 5) sourceC1195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 549) := by
    have ha : (tripleCharges (sourceA1195 + difference 5 0) (sourceB1195 + difference 0 5) sourceC1195) = raw20036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1195 sourceB1195 sourceC1195 difference raw20036; decide +kernel
    rw [ha]
    exact (canonical20036 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1195 + sourceB1195) sourceC1195) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1195 + sourceB1195) sourceC1195) = raw20037 := by
      apply Matrix.ext; unfold doubleCharges sourceA1195 sourceB1195 sourceC1195 raw20037; decide +kernel
    rw [ha]
    exact (canonical20037 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1195 sourceB1195 sourceC1195
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1195, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1196 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1196 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1196 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceForm1196 : Integer.Sparse Master := [(Sum.inr 570, 1), (Sum.inr 701, 2), (Sum.inr 723, 1), (Sum.inr 817, 1), (Sum.inr 1002, 1), (Sum.inr 4070, -1)]

theorem sourceEq1196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1196 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1196 + difference 1 0) (sourceB1196 + difference 0 1) sourceC1196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 570) := by
    have ha : (tripleCharges (sourceA1196 + difference 1 0) (sourceB1196 + difference 0 1) sourceC1196) = raw20032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1196 sourceB1196 sourceC1196 difference raw20032; decide +kernel
    rw [ha]
    exact (canonical20032 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1196 + difference 1 1) (sourceB1196 + difference 1 1) sourceC1196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 817) := by
    have ha : (tripleCharges (sourceA1196 + difference 1 1) (sourceB1196 + difference 1 1) sourceC1196) = raw20031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1196 sourceB1196 sourceC1196 difference raw20031; decide +kernel
    rw [ha]
    exact (canonical20031 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1196 + difference 1 2) (sourceB1196 + difference 2 1) sourceC1196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 701) := by
    have ha : (tripleCharges (sourceA1196 + difference 1 2) (sourceB1196 + difference 2 1) sourceC1196) = raw20038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1196 sourceB1196 sourceC1196 difference raw20038; decide +kernel
    rw [ha]
    exact (canonical20038 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1196 + difference 1 3) (sourceB1196 + difference 3 1) sourceC1196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 701) := by
    have ha : (tripleCharges (sourceA1196 + difference 1 3) (sourceB1196 + difference 3 1) sourceC1196) = raw20039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1196 sourceB1196 sourceC1196 difference raw20039; decide +kernel
    rw [ha]
    exact (canonical20039 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1196 + difference 1 4) (sourceB1196 + difference 4 1) sourceC1196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 723) := by
    have ha : (tripleCharges (sourceA1196 + difference 1 4) (sourceB1196 + difference 4 1) sourceC1196) = raw20040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1196 sourceB1196 sourceC1196 difference raw20040; decide +kernel
    rw [ha]
    exact (canonical20040 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1196 + difference 1 5) (sourceB1196 + difference 5 1) sourceC1196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1002) := by
    have ha : (tripleCharges (sourceA1196 + difference 1 5) (sourceB1196 + difference 5 1) sourceC1196) = raw20041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1196 sourceB1196 sourceC1196 difference raw20041; decide +kernel
    rw [ha]
    exact (canonical20041 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1196 + sourceB1196) sourceC1196) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1196 + sourceB1196) sourceC1196) = raw20037 := by
      apply Matrix.ext; unfold doubleCharges sourceA1196 sourceB1196 sourceC1196 raw20037; decide +kernel
    rw [ha]
    exact (canonical20037 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1196 sourceB1196 sourceC1196
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1196, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1197 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1197 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1197 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceForm1197 : Integer.Sparse Master := [(Sum.inr 540, 1), (Sum.inr 701, 2), (Sum.inr 735, 1), (Sum.inr 809, 1), (Sum.inr 817, 1), (Sum.inr 4070, -1)]

theorem sourceEq1197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1197 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1197 + difference 0 1) (sourceB1197 + difference 1 0) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1197 + difference 0 1) (sourceB1197 + difference 1 0) sourceC1197) = raw20042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20042; decide +kernel
    rw [ha]
    exact (canonical20042 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1197 + difference 1 1) (sourceB1197 + difference 1 1) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 817) := by
    have ha : (tripleCharges (sourceA1197 + difference 1 1) (sourceB1197 + difference 1 1) sourceC1197) = raw20031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20031; decide +kernel
    rw [ha]
    exact (canonical20031 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1197 + difference 2 1) (sourceB1197 + difference 1 2) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 701) := by
    have ha : (tripleCharges (sourceA1197 + difference 2 1) (sourceB1197 + difference 1 2) sourceC1197) = raw20043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20043; decide +kernel
    rw [ha]
    exact (canonical20043 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1197 + difference 3 1) (sourceB1197 + difference 1 3) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 701) := by
    have ha : (tripleCharges (sourceA1197 + difference 3 1) (sourceB1197 + difference 1 3) sourceC1197) = raw20044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20044; decide +kernel
    rw [ha]
    exact (canonical20044 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1197 + difference 4 1) (sourceB1197 + difference 1 4) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 735) := by
    have ha : (tripleCharges (sourceA1197 + difference 4 1) (sourceB1197 + difference 1 4) sourceC1197) = raw20045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20045; decide +kernel
    rw [ha]
    exact (canonical20045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1197 + difference 5 1) (sourceB1197 + difference 1 5) sourceC1197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 540) := by
    have ha : (tripleCharges (sourceA1197 + difference 5 1) (sourceB1197 + difference 1 5) sourceC1197) = raw20046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1197 sourceB1197 sourceC1197 difference raw20046; decide +kernel
    rw [ha]
    exact (canonical20046 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1197 + sourceB1197) sourceC1197) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1197 + sourceB1197) sourceC1197) = raw20037 := by
      apply Matrix.ext; unfold doubleCharges sourceA1197 sourceB1197 sourceC1197 raw20037; decide +kernel
    rw [ha]
    exact (canonical20037 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1197 sourceB1197 sourceC1197
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1197, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1198 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1198 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1198 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceForm1198 : Integer.Sparse Master := [(Sum.inr 596, 1), (Sum.inr 735, 3), (Sum.inr 817, 1), (Sum.inr 1077, 1), (Sum.inr 4070, -1)]

theorem sourceEq1198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1198 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 0) (sourceB1198 + difference 0 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 596) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 0) (sourceB1198 + difference 0 4) sourceC1198) = raw20035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20035; decide +kernel
    rw [ha]
    exact (canonical20035 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 1) (sourceB1198 + difference 1 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 735) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 1) (sourceB1198 + difference 1 4) sourceC1198) = raw20045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20045; decide +kernel
    rw [ha]
    exact (canonical20045 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 2) (sourceB1198 + difference 2 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 735) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 2) (sourceB1198 + difference 2 4) sourceC1198) = raw20047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20047; decide +kernel
    rw [ha]
    exact (canonical20047 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 3) (sourceB1198 + difference 3 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 735) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 3) (sourceB1198 + difference 3 4) sourceC1198) = raw20048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20048; decide +kernel
    rw [ha]
    exact (canonical20048 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 4) (sourceB1198 + difference 4 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 817) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 4) (sourceB1198 + difference 4 4) sourceC1198) = raw20031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20031; decide +kernel
    rw [ha]
    exact (canonical20031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1198 + difference 4 5) (sourceB1198 + difference 5 4) sourceC1198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1077) := by
    have ha : (tripleCharges (sourceA1198 + difference 4 5) (sourceB1198 + difference 5 4) sourceC1198) = raw20049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1198 sourceB1198 sourceC1198 difference raw20049; decide +kernel
    rw [ha]
    exact (canonical20049 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1198 + sourceB1198) sourceC1198) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1198 + sourceB1198) sourceC1198) = raw20037 := by
      apply Matrix.ext; unfold doubleCharges sourceA1198 sourceB1198 sourceC1198 raw20037; decide +kernel
    rw [ha]
    exact (canonical20037 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1198 sourceB1198 sourceC1198
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1198, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1199 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceB1199 : Charge := ![3, 0, 0, 0, 1, -4]
def sourceC1199 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1199 : Integer.Sparse Master := [(Sum.inr 4072, 1), (Sum.inr 4116, 3), (Sum.inr 4124, 1), (Sum.inr 4135, 1), (Sum.inr 4208, 6), (Sum.inr 4215, 3), (Sum.inr 4226, 3), (Sum.inr 4257, 3), (Sum.inr 4274, 3), (Sum.inr 4280, 1), (Sum.inr 4405, 3), (Sum.inr 4468, 1), (Sum.inr 4512, 1)]

theorem sourceEq1199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1199 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1199 + difference 0 1) (sourceB1199 + difference 1 0) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA1199 + difference 0 1) (sourceB1199 + difference 1 0) sourceC1199) = raw19768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19768; decide +kernel
    rw [ha]
    exact (canonical19768 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1199 + difference 0 2) (sourceB1199 + difference 2 0) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA1199 + difference 0 2) (sourceB1199 + difference 2 0) sourceC1199) = raw19769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19769; decide +kernel
    rw [ha]
    exact (canonical19769 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1199 + difference 0 3) (sourceB1199 + difference 3 0) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA1199 + difference 0 3) (sourceB1199 + difference 3 0) sourceC1199) = raw19770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19770; decide +kernel
    rw [ha]
    exact (canonical19770 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1199 + difference 0 4) (sourceB1199 + difference 4 0) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4280) := by
    have ha : (tripleCharges (sourceA1199 + difference 0 4) (sourceB1199 + difference 4 0) sourceC1199) = raw19771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19771; decide +kernel
    rw [ha]
    exact (canonical19771 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1199 + difference 0 5) (sourceB1199 + difference 5 0) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1199 + difference 0 5) (sourceB1199 + difference 5 0) sourceC1199) = raw19584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19584; decide +kernel
    rw [ha]
    exact (canonical19584 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1199 + difference 1 0) (sourceB1199 + difference 0 1) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4215) := by
    have ha : (tripleCharges (sourceA1199 + difference 1 0) (sourceB1199 + difference 0 1) sourceC1199) = raw20050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20050; decide +kernel
    rw [ha]
    exact (canonical20050 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1199 + difference 1 2) (sourceB1199 + difference 2 1) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4208) := by
    have ha : (tripleCharges (sourceA1199 + difference 1 2) (sourceB1199 + difference 2 1) sourceC1199) = raw20051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20051; decide +kernel
    rw [ha]
    exact (canonical20051 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1199 + difference 1 3) (sourceB1199 + difference 3 1) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4208) := by
    have ha : (tripleCharges (sourceA1199 + difference 1 3) (sourceB1199 + difference 3 1) sourceC1199) = raw20052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20052; decide +kernel
    rw [ha]
    exact (canonical20052 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1199 + difference 1 4) (sourceB1199 + difference 4 1) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4226) := by
    have ha : (tripleCharges (sourceA1199 + difference 1 4) (sourceB1199 + difference 4 1) sourceC1199) = raw20053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20053; decide +kernel
    rw [ha]
    exact (canonical20053 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1199 + difference 1 5) (sourceB1199 + difference 5 1) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1199 + difference 1 5) (sourceB1199 + difference 5 1) sourceC1199) = raw19754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19754; decide +kernel
    rw [ha]
    exact (canonical19754 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1199 + difference 2 0) (sourceB1199 + difference 0 2) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4215) := by
    have ha : (tripleCharges (sourceA1199 + difference 2 0) (sourceB1199 + difference 0 2) sourceC1199) = raw20054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20054; decide +kernel
    rw [ha]
    exact (canonical20054 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1199 + difference 2 1) (sourceB1199 + difference 1 2) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4208) := by
    have ha : (tripleCharges (sourceA1199 + difference 2 1) (sourceB1199 + difference 1 2) sourceC1199) = raw20055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20055; decide +kernel
    rw [ha]
    exact (canonical20055 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1199 + difference 2 3) (sourceB1199 + difference 3 2) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4208) := by
    have ha : (tripleCharges (sourceA1199 + difference 2 3) (sourceB1199 + difference 3 2) sourceC1199) = raw20056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20056; decide +kernel
    rw [ha]
    exact (canonical20056 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1199 + difference 2 4) (sourceB1199 + difference 4 2) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4226) := by
    have ha : (tripleCharges (sourceA1199 + difference 2 4) (sourceB1199 + difference 4 2) sourceC1199) = raw20057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20057; decide +kernel
    rw [ha]
    exact (canonical20057 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1199 + difference 2 5) (sourceB1199 + difference 5 2) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1199 + difference 2 5) (sourceB1199 + difference 5 2) sourceC1199) = raw19758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19758; decide +kernel
    rw [ha]
    exact (canonical19758 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1199 + difference 3 0) (sourceB1199 + difference 0 3) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4215) := by
    have ha : (tripleCharges (sourceA1199 + difference 3 0) (sourceB1199 + difference 0 3) sourceC1199) = raw20058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20058; decide +kernel
    rw [ha]
    exact (canonical20058 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1199 + difference 3 1) (sourceB1199 + difference 1 3) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4208) := by
    have ha : (tripleCharges (sourceA1199 + difference 3 1) (sourceB1199 + difference 1 3) sourceC1199) = raw20059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20059; decide +kernel
    rw [ha]
    exact (canonical20059 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1199 + difference 3 2) (sourceB1199 + difference 2 3) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4208) := by
    have ha : (tripleCharges (sourceA1199 + difference 3 2) (sourceB1199 + difference 2 3) sourceC1199) = raw20060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20060; decide +kernel
    rw [ha]
    exact (canonical20060 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1199 + difference 3 4) (sourceB1199 + difference 4 3) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4226) := by
    have ha : (tripleCharges (sourceA1199 + difference 3 4) (sourceB1199 + difference 4 3) sourceC1199) = raw20061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20061; decide +kernel
    rw [ha]
    exact (canonical20061 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1199 + difference 3 5) (sourceB1199 + difference 5 3) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1199 + difference 3 5) (sourceB1199 + difference 5 3) sourceC1199) = raw19762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19762; decide +kernel
    rw [ha]
    exact (canonical19762 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1199 + difference 4 0) (sourceB1199 + difference 0 4) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (tripleCharges (sourceA1199 + difference 4 0) (sourceB1199 + difference 0 4) sourceC1199) = raw19967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19967; decide +kernel
    rw [ha]
    exact (canonical19967 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1199 + difference 4 1) (sourceB1199 + difference 1 4) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1199 + difference 4 1) (sourceB1199 + difference 1 4) sourceC1199) = raw19968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19968; decide +kernel
    rw [ha]
    exact (canonical19968 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1199 + difference 4 2) (sourceB1199 + difference 2 4) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1199 + difference 4 2) (sourceB1199 + difference 2 4) sourceC1199) = raw19969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19969; decide +kernel
    rw [ha]
    exact (canonical19969 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1199 + difference 4 3) (sourceB1199 + difference 3 4) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1199 + difference 4 3) (sourceB1199 + difference 3 4) sourceC1199) = raw19970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19970; decide +kernel
    rw [ha]
    exact (canonical19970 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1199 + difference 4 5) (sourceB1199 + difference 5 4) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4512) := by
    have ha : (tripleCharges (sourceA1199 + difference 4 5) (sourceB1199 + difference 5 4) sourceC1199) = raw19580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw19580; decide +kernel
    rw [ha]
    exact (canonical19580 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1199 + difference 5 0) (sourceB1199 + difference 0 5) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4124) := by
    have ha : (tripleCharges (sourceA1199 + difference 5 0) (sourceB1199 + difference 0 5) sourceC1199) = raw20062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20062; decide +kernel
    rw [ha]
    exact (canonical20062 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1199 + difference 5 1) (sourceB1199 + difference 1 5) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4116) := by
    have ha : (tripleCharges (sourceA1199 + difference 5 1) (sourceB1199 + difference 1 5) sourceC1199) = raw20063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20063; decide +kernel
    rw [ha]
    exact (canonical20063 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1199 + difference 5 2) (sourceB1199 + difference 2 5) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4116) := by
    have ha : (tripleCharges (sourceA1199 + difference 5 2) (sourceB1199 + difference 2 5) sourceC1199) = raw20064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20064; decide +kernel
    rw [ha]
    exact (canonical20064 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1199 + difference 5 3) (sourceB1199 + difference 3 5) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4116) := by
    have ha : (tripleCharges (sourceA1199 + difference 5 3) (sourceB1199 + difference 3 5) sourceC1199) = raw20065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20065; decide +kernel
    rw [ha]
    exact (canonical20065 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1199 + difference 5 4) (sourceB1199 + difference 4 5) sourceC1199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4135) := by
    have ha : (tripleCharges (sourceA1199 + difference 5 4) (sourceB1199 + difference 4 5) sourceC1199) = raw20066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1199 sourceB1199 sourceC1199 difference raw20066; decide +kernel
    rw [ha]
    exact (canonical20066 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1199 sourceB1199 sourceC1199
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1199, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1200 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1200 : Charge := ![4, 0, 0, 0, 0, -4]
def sourceC1200 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm1200 : Integer.Sparse Master := [(Sum.inr 4060, 8), (Sum.inr 4062, 1), (Sum.inr 4066, 12), (Sum.inr 4070, 8), (Sum.inr 4085, 1)]

theorem sourceEq1200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1200 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1200 + difference 0 1) (sourceB1200 + difference 1 0) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 0 1) (sourceB1200 + difference 1 0) sourceC1200) = raw5214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5214; decide +kernel
    rw [ha]
    exact (canonical5214 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1200 + difference 0 2) (sourceB1200 + difference 2 0) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 0 2) (sourceB1200 + difference 2 0) sourceC1200) = raw5215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5215; decide +kernel
    rw [ha]
    exact (canonical5215 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1200 + difference 0 3) (sourceB1200 + difference 3 0) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 0 3) (sourceB1200 + difference 3 0) sourceC1200) = raw5216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5216; decide +kernel
    rw [ha]
    exact (canonical5216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1200 + difference 0 4) (sourceB1200 + difference 4 0) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 0 4) (sourceB1200 + difference 4 0) sourceC1200) = raw5217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5217; decide +kernel
    rw [ha]
    exact (canonical5217 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1200 + difference 0 5) (sourceB1200 + difference 5 0) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA1200 + difference 0 5) (sourceB1200 + difference 5 0) sourceC1200) = raw2934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw2934; decide +kernel
    rw [ha]
    exact (canonical2934 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1200 + difference 1 0) (sourceB1200 + difference 0 1) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 1 0) (sourceB1200 + difference 0 1) sourceC1200) = raw20067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20067; decide +kernel
    rw [ha]
    exact (canonical20067 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1200 + difference 1 2) (sourceB1200 + difference 2 1) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 1 2) (sourceB1200 + difference 2 1) sourceC1200) = raw20068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20068; decide +kernel
    rw [ha]
    exact (canonical20068 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1200 + difference 1 3) (sourceB1200 + difference 3 1) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 1 3) (sourceB1200 + difference 3 1) sourceC1200) = raw20069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20069; decide +kernel
    rw [ha]
    exact (canonical20069 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1200 + difference 1 4) (sourceB1200 + difference 4 1) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 1 4) (sourceB1200 + difference 4 1) sourceC1200) = raw20070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20070; decide +kernel
    rw [ha]
    exact (canonical20070 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1200 + difference 1 5) (sourceB1200 + difference 5 1) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 1 5) (sourceB1200 + difference 5 1) sourceC1200) = raw5197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5197; decide +kernel
    rw [ha]
    exact (canonical5197 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1200 + difference 2 0) (sourceB1200 + difference 0 2) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 2 0) (sourceB1200 + difference 0 2) sourceC1200) = raw20071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20071; decide +kernel
    rw [ha]
    exact (canonical20071 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1200 + difference 2 1) (sourceB1200 + difference 1 2) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 2 1) (sourceB1200 + difference 1 2) sourceC1200) = raw20072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20072; decide +kernel
    rw [ha]
    exact (canonical20072 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1200 + difference 2 3) (sourceB1200 + difference 3 2) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 2 3) (sourceB1200 + difference 3 2) sourceC1200) = raw20073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20073; decide +kernel
    rw [ha]
    exact (canonical20073 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1200 + difference 2 4) (sourceB1200 + difference 4 2) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 2 4) (sourceB1200 + difference 4 2) sourceC1200) = raw20074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20074; decide +kernel
    rw [ha]
    exact (canonical20074 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1200 + difference 2 5) (sourceB1200 + difference 5 2) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 2 5) (sourceB1200 + difference 5 2) sourceC1200) = raw5201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5201; decide +kernel
    rw [ha]
    exact (canonical5201 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1200 + difference 3 0) (sourceB1200 + difference 0 3) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 3 0) (sourceB1200 + difference 0 3) sourceC1200) = raw20075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20075; decide +kernel
    rw [ha]
    exact (canonical20075 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1200 + difference 3 1) (sourceB1200 + difference 1 3) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 3 1) (sourceB1200 + difference 1 3) sourceC1200) = raw20076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20076; decide +kernel
    rw [ha]
    exact (canonical20076 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1200 + difference 3 2) (sourceB1200 + difference 2 3) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 3 2) (sourceB1200 + difference 2 3) sourceC1200) = raw20077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20077; decide +kernel
    rw [ha]
    exact (canonical20077 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1200 + difference 3 4) (sourceB1200 + difference 4 3) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 3 4) (sourceB1200 + difference 4 3) sourceC1200) = raw20078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20078; decide +kernel
    rw [ha]
    exact (canonical20078 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1200 + difference 3 5) (sourceB1200 + difference 5 3) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 3 5) (sourceB1200 + difference 5 3) sourceC1200) = raw5205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5205; decide +kernel
    rw [ha]
    exact (canonical5205 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1200 + difference 4 0) (sourceB1200 + difference 0 4) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 4 0) (sourceB1200 + difference 0 4) sourceC1200) = raw20079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20079; decide +kernel
    rw [ha]
    exact (canonical20079 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1200 + difference 4 1) (sourceB1200 + difference 1 4) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 4 1) (sourceB1200 + difference 1 4) sourceC1200) = raw20080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20080; decide +kernel
    rw [ha]
    exact (canonical20080 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1200 + difference 4 2) (sourceB1200 + difference 2 4) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 4 2) (sourceB1200 + difference 2 4) sourceC1200) = raw20081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20081; decide +kernel
    rw [ha]
    exact (canonical20081 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1200 + difference 4 3) (sourceB1200 + difference 3 4) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1200 + difference 4 3) (sourceB1200 + difference 3 4) sourceC1200) = raw20082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20082; decide +kernel
    rw [ha]
    exact (canonical20082 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1200 + difference 4 5) (sourceB1200 + difference 5 4) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1200 + difference 4 5) (sourceB1200 + difference 5 4) sourceC1200) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1200 + difference 5 0) (sourceB1200 + difference 0 5) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4062) := by
    have ha : (tripleCharges (sourceA1200 + difference 5 0) (sourceB1200 + difference 0 5) sourceC1200) = raw20083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20083; decide +kernel
    rw [ha]
    exact (canonical20083 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1200 + difference 5 1) (sourceB1200 + difference 1 5) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 5 1) (sourceB1200 + difference 1 5) sourceC1200) = raw20084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20084; decide +kernel
    rw [ha]
    exact (canonical20084 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1200 + difference 5 2) (sourceB1200 + difference 2 5) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 5 2) (sourceB1200 + difference 2 5) sourceC1200) = raw20085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20085; decide +kernel
    rw [ha]
    exact (canonical20085 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1200 + difference 5 3) (sourceB1200 + difference 3 5) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 5 3) (sourceB1200 + difference 3 5) sourceC1200) = raw20086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20086; decide +kernel
    rw [ha]
    exact (canonical20086 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1200 + difference 5 4) (sourceB1200 + difference 4 5) sourceC1200) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1200 + difference 5 4) (sourceB1200 + difference 4 5) sourceC1200) = raw20087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1200 sourceB1200 sourceC1200 difference raw20087; decide +kernel
    rw [ha]
    exact (canonical20087 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1200 sourceB1200 sourceC1200
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1200, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1201 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1201 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC1201 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm1201 : Integer.Sparse Master := [(Sum.inr 621, 1), (Sum.inr 940, 3), (Sum.inr 1092, 1), (Sum.inr 1094, 1), (Sum.inr 4085, -1)]

theorem sourceEq1201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1201 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 0) (sourceB1201 + difference 0 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 621) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 0) (sourceB1201 + difference 0 4) sourceC1201) = raw20088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw20088; decide +kernel
    rw [ha]
    exact (canonical20088 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 1) (sourceB1201 + difference 1 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 940) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 1) (sourceB1201 + difference 1 4) sourceC1201) = raw20089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw20089; decide +kernel
    rw [ha]
    exact (canonical20089 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 2) (sourceB1201 + difference 2 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 940) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 2) (sourceB1201 + difference 2 4) sourceC1201) = raw20090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw20090; decide +kernel
    rw [ha]
    exact (canonical20090 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 3) (sourceB1201 + difference 3 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 940) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 3) (sourceB1201 + difference 3 4) sourceC1201) = raw20091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw20091; decide +kernel
    rw [ha]
    exact (canonical20091 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 4) (sourceB1201 + difference 4 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 4) (sourceB1201 + difference 4 4) sourceC1201) = raw3521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw3521; decide +kernel
    rw [ha]
    exact (canonical3521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 5) (sourceB1201 + difference 5 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 5) (sourceB1201 + difference 5 4) sourceC1201) = raw20092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw20092; decide +kernel
    rw [ha]
    exact (canonical20092 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1201 + sourceB1201) sourceC1201) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1201 + sourceB1201) sourceC1201) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA1201 sourceB1201 sourceC1201 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1201 sourceB1201 sourceC1201
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1201, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1202 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB1202 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1202 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1202 : Integer.Sparse Master := [(Sum.inr 1093, 1), (Sum.inr 1747, 1), (Sum.inr 2064, 3), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

theorem sourceEq1202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1202 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 0) (sourceB1202 + difference 0 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 0) (sourceB1202 + difference 0 0) sourceC1202) = raw20093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20093; decide +kernel
    rw [ha]
    exact (canonical20093 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 1) (sourceB1202 + difference 1 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2064) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 1) (sourceB1202 + difference 1 0) sourceC1202) = raw20094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20094; decide +kernel
    rw [ha]
    exact (canonical20094 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 2) (sourceB1202 + difference 2 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2064) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 2) (sourceB1202 + difference 2 0) sourceC1202) = raw20095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20095; decide +kernel
    rw [ha]
    exact (canonical20095 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 3) (sourceB1202 + difference 3 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2064) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 3) (sourceB1202 + difference 3 0) sourceC1202) = raw20096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20096; decide +kernel
    rw [ha]
    exact (canonical20096 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 4) (sourceB1202 + difference 4 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 4) (sourceB1202 + difference 4 0) sourceC1202) = raw20097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20097; decide +kernel
    rw [ha]
    exact (canonical20097 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 5) (sourceB1202 + difference 5 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1093) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 5) (sourceB1202 + difference 5 0) sourceC1202) = raw20098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20098; decide +kernel
    rw [ha]
    exact (canonical20098 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1202 + sourceB1202) sourceC1202) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1202 + sourceB1202) sourceC1202) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1202 sourceB1202 sourceC1202 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1202 sourceB1202 sourceC1202
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1202, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1203 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB1203 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1203 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1203 : Integer.Sparse Master := [(Sum.inr 1745, 3), (Sum.inr 1747, 1), (Sum.inr 1756, 1), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

theorem sourceEq1203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1203 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1203 + difference 0 4) (sourceB1203 + difference 4 0) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1203 + difference 0 4) (sourceB1203 + difference 4 0) sourceC1203) = raw20097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20097; decide +kernel
    rw [ha]
    exact (canonical20097 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1203 + difference 1 4) (sourceB1203 + difference 4 1) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1203 + difference 1 4) (sourceB1203 + difference 4 1) sourceC1203) = raw20100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20100; decide +kernel
    rw [ha]
    exact (canonical20100 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1203 + difference 2 4) (sourceB1203 + difference 4 2) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1203 + difference 2 4) (sourceB1203 + difference 4 2) sourceC1203) = raw20101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20101; decide +kernel
    rw [ha]
    exact (canonical20101 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1203 + difference 3 4) (sourceB1203 + difference 4 3) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1203 + difference 3 4) (sourceB1203 + difference 4 3) sourceC1203) = raw20102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20102; decide +kernel
    rw [ha]
    exact (canonical20102 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1203 + difference 4 4) (sourceB1203 + difference 4 4) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA1203 + difference 4 4) (sourceB1203 + difference 4 4) sourceC1203) = raw20093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20093; decide +kernel
    rw [ha]
    exact (canonical20093 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1203 + difference 5 4) (sourceB1203 + difference 4 5) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1203 + difference 5 4) (sourceB1203 + difference 4 5) sourceC1203) = raw20103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20103; decide +kernel
    rw [ha]
    exact (canonical20103 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1203 + sourceB1203) sourceC1203) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1203 + sourceB1203) sourceC1203) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1203 sourceB1203 sourceC1203 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1203 sourceB1203 sourceC1203
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1203, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1204 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB1204 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1204 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1204 : Integer.Sparse Master := [(Sum.inr 860, 1), (Sum.inr 1628, 3), (Sum.inr 1747, 1), (Sum.inr 1756, 1), (Sum.inr 4070, -1)]

theorem sourceEq1204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1204 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 0) (sourceB1204 + difference 0 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 860) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 0) (sourceB1204 + difference 0 5) sourceC1204) = raw20104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20104; decide +kernel
    rw [ha]
    exact (canonical20104 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 1) (sourceB1204 + difference 1 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1628) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 1) (sourceB1204 + difference 1 5) sourceC1204) = raw20105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20105; decide +kernel
    rw [ha]
    exact (canonical20105 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 2) (sourceB1204 + difference 2 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1628) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 2) (sourceB1204 + difference 2 5) sourceC1204) = raw20106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20106; decide +kernel
    rw [ha]
    exact (canonical20106 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 3) (sourceB1204 + difference 3 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1628) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 3) (sourceB1204 + difference 3 5) sourceC1204) = raw20107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20107; decide +kernel
    rw [ha]
    exact (canonical20107 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 4) (sourceB1204 + difference 4 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 4) (sourceB1204 + difference 4 5) sourceC1204) = raw20103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20103; decide +kernel
    rw [ha]
    exact (canonical20103 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 5) (sourceB1204 + difference 5 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 5) (sourceB1204 + difference 5 5) sourceC1204) = raw20093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20093; decide +kernel
    rw [ha]
    exact (canonical20093 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1204 + sourceB1204) sourceC1204) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1204 + sourceB1204) sourceC1204) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1204 sourceB1204 sourceC1204 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1204 sourceB1204 sourceC1204
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1204, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1205 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1205 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC1205 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm1205 : Integer.Sparse Master := [(Sum.inr 612, 1), (Sum.inr 931, 2), (Sum.inr 1047, 1), (Sum.inr 1061, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

theorem sourceEq1205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1205 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 0) (sourceB1205 + difference 0 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 612) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 0) (sourceB1205 + difference 0 3) sourceC1205) = raw20108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw20108; decide +kernel
    rw [ha]
    exact (canonical20108 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 1) (sourceB1205 + difference 1 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 931) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 1) (sourceB1205 + difference 1 3) sourceC1205) = raw20109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw20109; decide +kernel
    rw [ha]
    exact (canonical20109 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 2) (sourceB1205 + difference 2 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 931) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 2) (sourceB1205 + difference 2 3) sourceC1205) = raw20110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw20110; decide +kernel
    rw [ha]
    exact (canonical20110 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 3) (sourceB1205 + difference 3 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 3) (sourceB1205 + difference 3 3) sourceC1205) = raw3634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw3634; decide +kernel
    rw [ha]
    exact (canonical3634 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 4) (sourceB1205 + difference 4 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 4) (sourceB1205 + difference 4 3) sourceC1205) = raw3633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw3633; decide +kernel
    rw [ha]
    exact (canonical3633 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 5) (sourceB1205 + difference 5 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 5) (sourceB1205 + difference 5 3) sourceC1205) = raw20111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw20111; decide +kernel
    rw [ha]
    exact (canonical20111 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1205 + sourceB1205) sourceC1205) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1205 + sourceB1205) sourceC1205) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA1205 sourceB1205 sourceC1205 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1205 sourceB1205 sourceC1205
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1205, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1206 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1206 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC1206 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm1206 : Integer.Sparse Master := [(Sum.inr 590, 1), (Sum.inr 914, 2), (Sum.inr 954, 1), (Sum.inr 1047, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

theorem sourceEq1206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1206 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 0) (sourceB1206 + difference 0 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 590) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 0) (sourceB1206 + difference 0 4) sourceC1206) = raw20112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw20112; decide +kernel
    rw [ha]
    exact (canonical20112 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 1) (sourceB1206 + difference 1 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 914) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 1) (sourceB1206 + difference 1 4) sourceC1206) = raw20113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw20113; decide +kernel
    rw [ha]
    exact (canonical20113 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 2) (sourceB1206 + difference 2 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 914) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 2) (sourceB1206 + difference 2 4) sourceC1206) = raw20114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw20114; decide +kernel
    rw [ha]
    exact (canonical20114 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 3) (sourceB1206 + difference 3 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 954) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 3) (sourceB1206 + difference 3 4) sourceC1206) = raw20115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw20115; decide +kernel
    rw [ha]
    exact (canonical20115 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 4) (sourceB1206 + difference 4 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 4) (sourceB1206 + difference 4 4) sourceC1206) = raw3634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw3634; decide +kernel
    rw [ha]
    exact (canonical3634 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 5) (sourceB1206 + difference 5 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 5) (sourceB1206 + difference 5 4) sourceC1206) = raw20116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw20116; decide +kernel
    rw [ha]
    exact (canonical20116 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1206 + sourceB1206) sourceC1206) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1206 + sourceB1206) sourceC1206) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA1206 sourceB1206 sourceC1206 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1206 sourceB1206 sourceC1206
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1206, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1207 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1207 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1207 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm1207 : Integer.Sparse Master := [(Sum.inr 951, 1), (Sum.inr 1336, 2), (Sum.inr 1348, 1), (Sum.inr 1408, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

theorem sourceEq1207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1207 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1207 + difference 0 3) (sourceB1207 + difference 3 0) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1207 + difference 0 3) (sourceB1207 + difference 3 0) sourceC1207) = raw4762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw4762; decide +kernel
    rw [ha]
    exact (canonical4762 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1207 + difference 1 3) (sourceB1207 + difference 3 1) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1336) := by
    have ha : (tripleCharges (sourceA1207 + difference 1 3) (sourceB1207 + difference 3 1) sourceC1207) = raw20117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw20117; decide +kernel
    rw [ha]
    exact (canonical20117 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1207 + difference 2 3) (sourceB1207 + difference 3 2) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1336) := by
    have ha : (tripleCharges (sourceA1207 + difference 2 3) (sourceB1207 + difference 3 2) sourceC1207) = raw20118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw20118; decide +kernel
    rw [ha]
    exact (canonical20118 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1207 + difference 3 3) (sourceB1207 + difference 3 3) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA1207 + difference 3 3) (sourceB1207 + difference 3 3) sourceC1207) = raw4748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw4748; decide +kernel
    rw [ha]
    exact (canonical4748 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1207 + difference 4 3) (sourceB1207 + difference 3 4) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1348) := by
    have ha : (tripleCharges (sourceA1207 + difference 4 3) (sourceB1207 + difference 3 4) sourceC1207) = raw20119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw20119; decide +kernel
    rw [ha]
    exact (canonical20119 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1207 + difference 5 3) (sourceB1207 + difference 3 5) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 951) := by
    have ha : (tripleCharges (sourceA1207 + difference 5 3) (sourceB1207 + difference 3 5) sourceC1207) = raw20120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw20120; decide +kernel
    rw [ha]
    exact (canonical20120 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1207 + sourceB1207) sourceC1207) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1207 + sourceB1207) sourceC1207) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA1207 sourceB1207 sourceC1207 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1207 sourceB1207 sourceC1207
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1207, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1208 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB1208 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1208 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1208 : Integer.Sparse Master := [(Sum.inr 1072, 1), (Sum.inr 1745, 1), (Sum.inr 2045, 2), (Sum.inr 2226, 1), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

theorem sourceEq1208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1208 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 0) (sourceB1208 + difference 0 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 0) (sourceB1208 + difference 0 0) sourceC1208) = raw20102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20102; decide +kernel
    rw [ha]
    exact (canonical20102 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 1) (sourceB1208 + difference 1 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2045) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 1) (sourceB1208 + difference 1 0) sourceC1208) = raw20121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20121; decide +kernel
    rw [ha]
    exact (canonical20121 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 2) (sourceB1208 + difference 2 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2045) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 2) (sourceB1208 + difference 2 0) sourceC1208) = raw20122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20122; decide +kernel
    rw [ha]
    exact (canonical20122 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 3) (sourceB1208 + difference 3 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 3) (sourceB1208 + difference 3 0) sourceC1208) = raw20097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20097; decide +kernel
    rw [ha]
    exact (canonical20097 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 4) (sourceB1208 + difference 4 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 4) (sourceB1208 + difference 4 0) sourceC1208) = raw20123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20123; decide +kernel
    rw [ha]
    exact (canonical20123 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 5) (sourceB1208 + difference 5 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1072) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 5) (sourceB1208 + difference 5 0) sourceC1208) = raw20124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20124; decide +kernel
    rw [ha]
    exact (canonical20124 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1208 + sourceB1208) sourceC1208) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1208 + sourceB1208) sourceC1208) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1208 sourceB1208 sourceC1208 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1208 sourceB1208 sourceC1208
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1208, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1209 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB1209 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1209 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1209 : Integer.Sparse Master := [(Sum.inr 834, 2), (Sum.inr 836, 1), (Sum.inr 838, 1), (Sum.inr 853, 1), (Sum.inr 1745, 1), (Sum.inr 4070, -1)]

theorem sourceEq1209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1209 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1209 + difference 0 0) (sourceB1209 + difference 0 0) sourceC1209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1209 + difference 0 0) (sourceB1209 + difference 0 0) sourceC1209) = raw20102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1209 sourceB1209 sourceC1209 difference raw20102; decide +kernel
    rw [ha]
    exact (canonical20102 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1209 + difference 1 0) (sourceB1209 + difference 0 1) sourceC1209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 834) := by
    have ha : (tripleCharges (sourceA1209 + difference 1 0) (sourceB1209 + difference 0 1) sourceC1209) = raw20125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1209 sourceB1209 sourceC1209 difference raw20125; decide +kernel
    rw [ha]
    exact (canonical20125 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1209 + difference 2 0) (sourceB1209 + difference 0 2) sourceC1209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 834) := by
    have ha : (tripleCharges (sourceA1209 + difference 2 0) (sourceB1209 + difference 0 2) sourceC1209) = raw20126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1209 sourceB1209 sourceC1209 difference raw20126; decide +kernel
    rw [ha]
    exact (canonical20126 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1209 + difference 3 0) (sourceB1209 + difference 0 3) sourceC1209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 838) := by
    have ha : (tripleCharges (sourceA1209 + difference 3 0) (sourceB1209 + difference 0 3) sourceC1209) = raw20127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1209 sourceB1209 sourceC1209 difference raw20127; decide +kernel
    rw [ha]
    exact (canonical20127 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1209 + difference 4 0) (sourceB1209 + difference 0 4) sourceC1209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 836) := by
    have ha : (tripleCharges (sourceA1209 + difference 4 0) (sourceB1209 + difference 0 4) sourceC1209) = raw20128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1209 sourceB1209 sourceC1209 difference raw20128; decide +kernel
    rw [ha]
    exact (canonical20128 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1209 + difference 5 0) (sourceB1209 + difference 0 5) sourceC1209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 853) := by
    have ha : (tripleCharges (sourceA1209 + difference 5 0) (sourceB1209 + difference 0 5) sourceC1209) = raw20129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1209 sourceB1209 sourceC1209 difference raw20129; decide +kernel
    rw [ha]
    exact (canonical20129 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1209 + sourceB1209) sourceC1209) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1209 + sourceB1209) sourceC1209) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1209 sourceB1209 sourceC1209 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1209 sourceB1209 sourceC1209
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1209, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1210 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB1210 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1210 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1210 : Integer.Sparse Master := [(Sum.inr 1744, 2), (Sum.inr 1745, 1), (Sum.inr 1746, 1), (Sum.inr 1750, 1), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

theorem sourceEq1210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1210 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1210 + difference 0 4) (sourceB1210 + difference 4 0) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1210 + difference 0 4) (sourceB1210 + difference 4 0) sourceC1210) = raw20123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20123; decide +kernel
    rw [ha]
    exact (canonical20123 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1210 + difference 1 4) (sourceB1210 + difference 4 1) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1210 + difference 1 4) (sourceB1210 + difference 4 1) sourceC1210) = raw20130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20130; decide +kernel
    rw [ha]
    exact (canonical20130 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1210 + difference 2 4) (sourceB1210 + difference 4 2) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1210 + difference 2 4) (sourceB1210 + difference 4 2) sourceC1210) = raw20131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20131; decide +kernel
    rw [ha]
    exact (canonical20131 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1210 + difference 3 4) (sourceB1210 + difference 4 3) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA1210 + difference 3 4) (sourceB1210 + difference 4 3) sourceC1210) = raw20132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20132; decide +kernel
    rw [ha]
    exact (canonical20132 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1210 + difference 4 4) (sourceB1210 + difference 4 4) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1210 + difference 4 4) (sourceB1210 + difference 4 4) sourceC1210) = raw20102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20102; decide +kernel
    rw [ha]
    exact (canonical20102 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1210 + difference 5 4) (sourceB1210 + difference 4 5) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1210 + difference 5 4) (sourceB1210 + difference 4 5) sourceC1210) = raw20133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20133; decide +kernel
    rw [ha]
    exact (canonical20133 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1210 + sourceB1210) sourceC1210) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1210 + sourceB1210) sourceC1210) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1210 sourceB1210 sourceC1210 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1210 sourceB1210 sourceC1210
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1210, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1211 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB1211 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1211 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1211 : Integer.Sparse Master := [(Sum.inr 853, 1), (Sum.inr 1619, 2), (Sum.inr 1745, 1), (Sum.inr 1750, 1), (Sum.inr 1756, 1), (Sum.inr 4070, -1)]

theorem sourceEq1211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1211 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 0) (sourceB1211 + difference 0 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 853) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 0) (sourceB1211 + difference 0 5) sourceC1211) = raw20129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20129; decide +kernel
    rw [ha]
    exact (canonical20129 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 1) (sourceB1211 + difference 1 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 1) (sourceB1211 + difference 1 5) sourceC1211) = raw20134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20134; decide +kernel
    rw [ha]
    exact (canonical20134 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 2) (sourceB1211 + difference 2 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 2) (sourceB1211 + difference 2 5) sourceC1211) = raw20135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20135; decide +kernel
    rw [ha]
    exact (canonical20135 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 3) (sourceB1211 + difference 3 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 3) (sourceB1211 + difference 3 5) sourceC1211) = raw20103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20103; decide +kernel
    rw [ha]
    exact (canonical20103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 4) (sourceB1211 + difference 4 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 4) (sourceB1211 + difference 4 5) sourceC1211) = raw20133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20133; decide +kernel
    rw [ha]
    exact (canonical20133 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 5) (sourceB1211 + difference 5 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 5) (sourceB1211 + difference 5 5) sourceC1211) = raw20102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20102; decide +kernel
    rw [ha]
    exact (canonical20102 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1211 + sourceB1211) sourceC1211) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1211 + sourceB1211) sourceC1211) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1211 sourceB1211 sourceC1211 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1211 sourceB1211 sourceC1211
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1211, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1212 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1212 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceC1212 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceForm1212 : Integer.Sparse Master := [(Sum.inr 606, 1), (Sum.inr 925, 2), (Sum.inr 1059, 1), (Sum.inr 1083, 1), (Sum.inr 1091, 1), (Sum.inr 4084, -1)]

theorem sourceEq1212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1212 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 0) (sourceB1212 + difference 0 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 606) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 0) (sourceB1212 + difference 0 3) sourceC1212) = raw20136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20136; decide +kernel
    rw [ha]
    exact (canonical20136 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 1) (sourceB1212 + difference 1 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 925) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 1) (sourceB1212 + difference 1 3) sourceC1212) = raw20137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20137; decide +kernel
    rw [ha]
    exact (canonical20137 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 2) (sourceB1212 + difference 2 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 925) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 2) (sourceB1212 + difference 2 3) sourceC1212) = raw20138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20138; decide +kernel
    rw [ha]
    exact (canonical20138 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 3) (sourceB1212 + difference 3 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 3) (sourceB1212 + difference 3 3) sourceC1212) = raw20139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20139; decide +kernel
    rw [ha]
    exact (canonical20139 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 4) (sourceB1212 + difference 4 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 4) (sourceB1212 + difference 4 3) sourceC1212) = raw20140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20140; decide +kernel
    rw [ha]
    exact (canonical20140 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 5) (sourceB1212 + difference 5 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 5) (sourceB1212 + difference 5 3) sourceC1212) = raw20141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20141; decide +kernel
    rw [ha]
    exact (canonical20141 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1212 + sourceB1212) sourceC1212) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1212 + sourceB1212) sourceC1212) = raw20142 := by
      apply Matrix.ext; unfold doubleCharges sourceA1212 sourceB1212 sourceC1212 raw20142; decide +kernel
    rw [ha]
    exact (canonical20142 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1212 sourceB1212 sourceC1212
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1212, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1213 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1213 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1213 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceForm1213 : Integer.Sparse Master := [(Sum.inr 1142, 1), (Sum.inr 1317, 2), (Sum.inr 1324, 1), (Sum.inr 1372, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

theorem sourceEq1213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1213 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1213 + difference 0 3) (sourceB1213 + difference 3 0) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1213 + difference 0 3) (sourceB1213 + difference 3 0) sourceC1213) = raw20143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw20143; decide +kernel
    rw [ha]
    exact (canonical20143 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1213 + difference 1 3) (sourceB1213 + difference 3 1) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1317) := by
    have ha : (tripleCharges (sourceA1213 + difference 1 3) (sourceB1213 + difference 3 1) sourceC1213) = raw20144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw20144; decide +kernel
    rw [ha]
    exact (canonical20144 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1213 + difference 2 3) (sourceB1213 + difference 3 2) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1317) := by
    have ha : (tripleCharges (sourceA1213 + difference 2 3) (sourceB1213 + difference 3 2) sourceC1213) = raw20145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw20145; decide +kernel
    rw [ha]
    exact (canonical20145 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1213 + difference 3 3) (sourceB1213 + difference 3 3) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA1213 + difference 3 3) (sourceB1213 + difference 3 3) sourceC1213) = raw8781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw8781; decide +kernel
    rw [ha]
    exact (canonical8781 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1213 + difference 4 3) (sourceB1213 + difference 3 4) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1324) := by
    have ha : (tripleCharges (sourceA1213 + difference 4 3) (sourceB1213 + difference 3 4) sourceC1213) = raw20146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw20146; decide +kernel
    rw [ha]
    exact (canonical20146 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1213 + difference 5 3) (sourceB1213 + difference 3 5) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1213 + difference 5 3) (sourceB1213 + difference 3 5) sourceC1213) = raw20147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw20147; decide +kernel
    rw [ha]
    exact (canonical20147 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1213 + sourceB1213) sourceC1213) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1213 + sourceB1213) sourceC1213) = raw8776 := by
      apply Matrix.ext; unfold doubleCharges sourceA1213 sourceB1213 sourceC1213 raw8776; decide +kernel
    rw [ha]
    exact (canonical8776 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1213 sourceB1213 sourceC1213
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1213, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1214 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1214 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1214 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1214 : Integer.Sparse Master := [(Sum.inr 1729, 1), (Sum.inr 1952, 1), (Sum.inr 3242, 2), (Sum.inr 3247, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

theorem sourceEq1214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1214 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 0) (sourceB1214 + difference 0 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 0) (sourceB1214 + difference 0 0) sourceC1214) = raw20148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20148; decide +kernel
    rw [ha]
    exact (canonical20148 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 1) (sourceB1214 + difference 1 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3242) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 1) (sourceB1214 + difference 1 0) sourceC1214) = raw20149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20149; decide +kernel
    rw [ha]
    exact (canonical20149 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 2) (sourceB1214 + difference 2 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3242) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 2) (sourceB1214 + difference 2 0) sourceC1214) = raw20150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20150; decide +kernel
    rw [ha]
    exact (canonical20150 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 3) (sourceB1214 + difference 3 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 3) (sourceB1214 + difference 3 0) sourceC1214) = raw20151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20151; decide +kernel
    rw [ha]
    exact (canonical20151 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 4) (sourceB1214 + difference 4 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3247) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 4) (sourceB1214 + difference 4 0) sourceC1214) = raw20152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20152; decide +kernel
    rw [ha]
    exact (canonical20152 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 5) (sourceB1214 + difference 5 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1952) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 5) (sourceB1214 + difference 5 0) sourceC1214) = raw20153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20153; decide +kernel
    rw [ha]
    exact (canonical20153 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1214 + sourceB1214) sourceC1214) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1214 + sourceB1214) sourceC1214) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1214 sourceB1214 sourceC1214 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1214 sourceB1214 sourceC1214
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1214, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1215 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1215 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1215 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1215 : Integer.Sparse Master := [(Sum.inr 808, 2), (Sum.inr 814, 1), (Sum.inr 815, 1), (Sum.inr 857, 1), (Sum.inr 1729, 1), (Sum.inr 4070, -1)]

theorem sourceEq1215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1215 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1215 + difference 0 0) (sourceB1215 + difference 0 0) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1215 + difference 0 0) (sourceB1215 + difference 0 0) sourceC1215) = raw20148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20148; decide +kernel
    rw [ha]
    exact (canonical20148 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1215 + difference 1 0) (sourceB1215 + difference 0 1) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 808) := by
    have ha : (tripleCharges (sourceA1215 + difference 1 0) (sourceB1215 + difference 0 1) sourceC1215) = raw20154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20154; decide +kernel
    rw [ha]
    exact (canonical20154 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1215 + difference 2 0) (sourceB1215 + difference 0 2) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 808) := by
    have ha : (tripleCharges (sourceA1215 + difference 2 0) (sourceB1215 + difference 0 2) sourceC1215) = raw20155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20155; decide +kernel
    rw [ha]
    exact (canonical20155 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1215 + difference 3 0) (sourceB1215 + difference 0 3) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 814) := by
    have ha : (tripleCharges (sourceA1215 + difference 3 0) (sourceB1215 + difference 0 3) sourceC1215) = raw20156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20156; decide +kernel
    rw [ha]
    exact (canonical20156 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1215 + difference 4 0) (sourceB1215 + difference 0 4) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 857) := by
    have ha : (tripleCharges (sourceA1215 + difference 4 0) (sourceB1215 + difference 0 4) sourceC1215) = raw20157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20157; decide +kernel
    rw [ha]
    exact (canonical20157 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1215 + difference 5 0) (sourceB1215 + difference 0 5) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 815) := by
    have ha : (tripleCharges (sourceA1215 + difference 5 0) (sourceB1215 + difference 0 5) sourceC1215) = raw20158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20158; decide +kernel
    rw [ha]
    exact (canonical20158 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1215 + sourceB1215) sourceC1215) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1215 + sourceB1215) sourceC1215) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1215 sourceB1215 sourceC1215 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1215 sourceB1215 sourceC1215
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1215, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
