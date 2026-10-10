import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA512 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB512 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC512 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm512 : Integer.Sparse Master := [(Sum.inr 1642, 1), (Sum.inr 1643, 1), (Sum.inr 1646, 2), (Sum.inr 1736, 1), (Sum.inr 3388, 1), (Sum.inr 3389, 1), (Sum.inr 3392, 2), (Sum.inr 3443, 1), (Sum.inr 3445, 2), (Sum.inr 3476, 1), (Sum.inr 3530, 2), (Sum.inr 3562, 2), (Sum.inr 3565, 2), (Sum.inr 3571, 1), (Sum.inr 3572, 2), (Sum.inr 3612, 2), (Sum.inr 3625, 1), (Sum.inr 3956, 1), (Sum.inr 3961, 2), (Sum.inr 3984, 1), (Sum.inr 4028, 1)]

theorem sourceEq512 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm512 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA512 + difference 0 1) (sourceB512 + difference 1 0) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA512 + difference 0 1) (sourceB512 + difference 1 0) sourceC512) = raw8977 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8977; decide +kernel
    rw [ha]
    exact (canonical8977 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA512 + difference 0 2) (sourceB512 + difference 2 0) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA512 + difference 0 2) (sourceB512 + difference 2 0) sourceC512) = raw8978 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8978; decide +kernel
    rw [ha]
    exact (canonical8978 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA512 + difference 0 3) (sourceB512 + difference 3 0) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA512 + difference 0 3) (sourceB512 + difference 3 0) sourceC512) = raw8979 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8979; decide +kernel
    rw [ha]
    exact (canonical8979 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA512 + difference 0 4) (sourceB512 + difference 4 0) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4028) := by
    have ha : (tripleCharges (sourceA512 + difference 0 4) (sourceB512 + difference 4 0) sourceC512) = raw8980 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8980; decide +kernel
    rw [ha]
    exact (canonical8980 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA512 + difference 0 5) (sourceB512 + difference 5 0) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA512 + difference 0 5) (sourceB512 + difference 5 0) sourceC512) = raw8981 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8981; decide +kernel
    rw [ha]
    exact (canonical8981 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA512 + difference 1 0) (sourceB512 + difference 0 1) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1642) := by
    have ha : (tripleCharges (sourceA512 + difference 1 0) (sourceB512 + difference 0 1) sourceC512) = raw8982 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8982; decide +kernel
    rw [ha]
    exact (canonical8982 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA512 + difference 1 2) (sourceB512 + difference 2 1) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA512 + difference 1 2) (sourceB512 + difference 2 1) sourceC512) = raw8983 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8983; decide +kernel
    rw [ha]
    exact (canonical8983 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA512 + difference 1 3) (sourceB512 + difference 3 1) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA512 + difference 1 3) (sourceB512 + difference 3 1) sourceC512) = raw8984 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8984; decide +kernel
    rw [ha]
    exact (canonical8984 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA512 + difference 1 4) (sourceB512 + difference 4 1) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA512 + difference 1 4) (sourceB512 + difference 4 1) sourceC512) = raw8985 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8985; decide +kernel
    rw [ha]
    exact (canonical8985 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA512 + difference 1 5) (sourceB512 + difference 5 1) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA512 + difference 1 5) (sourceB512 + difference 5 1) sourceC512) = raw8986 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8986; decide +kernel
    rw [ha]
    exact (canonical8986 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA512 + difference 2 0) (sourceB512 + difference 0 2) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1646) := by
    have ha : (tripleCharges (sourceA512 + difference 2 0) (sourceB512 + difference 0 2) sourceC512) = raw8987 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8987; decide +kernel
    rw [ha]
    exact (canonical8987 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA512 + difference 2 1) (sourceB512 + difference 1 2) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3445) := by
    have ha : (tripleCharges (sourceA512 + difference 2 1) (sourceB512 + difference 1 2) sourceC512) = raw8988 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8988; decide +kernel
    rw [ha]
    exact (canonical8988 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA512 + difference 2 3) (sourceB512 + difference 3 2) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA512 + difference 2 3) (sourceB512 + difference 3 2) sourceC512) = raw8989 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8989; decide +kernel
    rw [ha]
    exact (canonical8989 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA512 + difference 2 4) (sourceB512 + difference 4 2) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA512 + difference 2 4) (sourceB512 + difference 4 2) sourceC512) = raw8990 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8990; decide +kernel
    rw [ha]
    exact (canonical8990 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA512 + difference 2 5) (sourceB512 + difference 5 2) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA512 + difference 2 5) (sourceB512 + difference 5 2) sourceC512) = raw8991 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8991; decide +kernel
    rw [ha]
    exact (canonical8991 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA512 + difference 3 0) (sourceB512 + difference 0 3) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1646) := by
    have ha : (tripleCharges (sourceA512 + difference 3 0) (sourceB512 + difference 0 3) sourceC512) = raw8992 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8992; decide +kernel
    rw [ha]
    exact (canonical8992 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA512 + difference 3 1) (sourceB512 + difference 1 3) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3445) := by
    have ha : (tripleCharges (sourceA512 + difference 3 1) (sourceB512 + difference 1 3) sourceC512) = raw8993 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8993; decide +kernel
    rw [ha]
    exact (canonical8993 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA512 + difference 3 2) (sourceB512 + difference 2 3) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA512 + difference 3 2) (sourceB512 + difference 2 3) sourceC512) = raw8994 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8994; decide +kernel
    rw [ha]
    exact (canonical8994 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA512 + difference 3 4) (sourceB512 + difference 4 3) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA512 + difference 3 4) (sourceB512 + difference 4 3) sourceC512) = raw8995 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8995; decide +kernel
    rw [ha]
    exact (canonical8995 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA512 + difference 3 5) (sourceB512 + difference 5 3) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA512 + difference 3 5) (sourceB512 + difference 5 3) sourceC512) = raw8996 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8996; decide +kernel
    rw [ha]
    exact (canonical8996 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA512 + difference 4 0) (sourceB512 + difference 0 4) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA512 + difference 4 0) (sourceB512 + difference 0 4) sourceC512) = raw8997 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8997; decide +kernel
    rw [ha]
    exact (canonical8997 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA512 + difference 4 1) (sourceB512 + difference 1 4) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA512 + difference 4 1) (sourceB512 + difference 1 4) sourceC512) = raw8998 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8998; decide +kernel
    rw [ha]
    exact (canonical8998 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA512 + difference 4 2) (sourceB512 + difference 2 4) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA512 + difference 4 2) (sourceB512 + difference 2 4) sourceC512) = raw8999 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw8999; decide +kernel
    rw [ha]
    exact (canonical8999 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA512 + difference 4 3) (sourceB512 + difference 3 4) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA512 + difference 4 3) (sourceB512 + difference 3 4) sourceC512) = raw9000 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw9000; decide +kernel
    rw [ha]
    exact (canonical9000 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA512 + difference 4 5) (sourceB512 + difference 5 4) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA512 + difference 4 5) (sourceB512 + difference 5 4) sourceC512) = raw9001 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw9001; decide +kernel
    rw [ha]
    exact (canonical9001 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA512 + difference 5 0) (sourceB512 + difference 0 5) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1643) := by
    have ha : (tripleCharges (sourceA512 + difference 5 0) (sourceB512 + difference 0 5) sourceC512) = raw9002 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw9002; decide +kernel
    rw [ha]
    exact (canonical9002 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA512 + difference 5 1) (sourceB512 + difference 1 5) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3443) := by
    have ha : (tripleCharges (sourceA512 + difference 5 1) (sourceB512 + difference 1 5) sourceC512) = raw9003 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw9003; decide +kernel
    rw [ha]
    exact (canonical9003 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA512 + difference 5 2) (sourceB512 + difference 2 5) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA512 + difference 5 2) (sourceB512 + difference 2 5) sourceC512) = raw9004 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw9004; decide +kernel
    rw [ha]
    exact (canonical9004 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA512 + difference 5 3) (sourceB512 + difference 3 5) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA512 + difference 5 3) (sourceB512 + difference 3 5) sourceC512) = raw9005 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw9005; decide +kernel
    rw [ha]
    exact (canonical9005 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA512 + difference 5 4) (sourceB512 + difference 4 5) sourceC512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA512 + difference 5 4) (sourceB512 + difference 4 5) sourceC512) = raw9006 := by
      apply Matrix.ext; unfold tripleCharges sourceA512 sourceB512 sourceC512 difference raw9006; decide +kernel
    rw [ha]
    exact (canonical9006 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA512 sourceB512 sourceC512
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm512, Integer.Sparse.eval]
  linarith only [hs]

def sourceA513 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB513 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC513 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm513 : Integer.Sparse Master := [(Sum.inr 3078, 1), (Sum.inr 3885, 1), (Sum.inr 3953, 1), (Sum.inr 3958, 2), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

theorem sourceEq513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm513 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA513 + difference 0 0) (sourceB513 + difference 0 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA513 + difference 0 0) (sourceB513 + difference 0 0) sourceC513) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA513 + difference 0 1) (sourceB513 + difference 1 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA513 + difference 0 1) (sourceB513 + difference 1 0) sourceC513) = raw9008 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9008; decide +kernel
    rw [ha]
    exact (canonical9008 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA513 + difference 0 2) (sourceB513 + difference 2 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA513 + difference 0 2) (sourceB513 + difference 2 0) sourceC513) = raw9009 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9009; decide +kernel
    rw [ha]
    exact (canonical9009 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA513 + difference 0 3) (sourceB513 + difference 3 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA513 + difference 0 3) (sourceB513 + difference 3 0) sourceC513) = raw9010 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9010; decide +kernel
    rw [ha]
    exact (canonical9010 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA513 + difference 0 4) (sourceB513 + difference 4 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA513 + difference 0 4) (sourceB513 + difference 4 0) sourceC513) = raw9011 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9011; decide +kernel
    rw [ha]
    exact (canonical9011 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA513 + difference 0 5) (sourceB513 + difference 5 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA513 + difference 0 5) (sourceB513 + difference 5 0) sourceC513) = raw9012 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9012; decide +kernel
    rw [ha]
    exact (canonical9012 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA513 + sourceB513) sourceC513) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA513 + sourceB513) sourceC513) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA513 sourceB513 sourceC513 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA513 sourceB513 sourceC513
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm513, Integer.Sparse.eval]
  linarith only [hs]

def sourceA514 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB514 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC514 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm514 : Integer.Sparse Master := [(Sum.inr 1384, 1), (Sum.inr 1389, 1), (Sum.inr 1391, 1), (Sum.inr 1407, 2), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

theorem sourceEq514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm514 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA514 + difference 0 0) (sourceB514 + difference 0 0) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA514 + difference 0 0) (sourceB514 + difference 0 0) sourceC514) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA514 + difference 1 0) (sourceB514 + difference 0 1) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1384) := by
    have ha : (tripleCharges (sourceA514 + difference 1 0) (sourceB514 + difference 0 1) sourceC514) = raw9014 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9014; decide +kernel
    rw [ha]
    exact (canonical9014 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA514 + difference 2 0) (sourceB514 + difference 0 2) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1407) := by
    have ha : (tripleCharges (sourceA514 + difference 2 0) (sourceB514 + difference 0 2) sourceC514) = raw9015 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9015; decide +kernel
    rw [ha]
    exact (canonical9015 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA514 + difference 3 0) (sourceB514 + difference 0 3) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1407) := by
    have ha : (tripleCharges (sourceA514 + difference 3 0) (sourceB514 + difference 0 3) sourceC514) = raw9016 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9016; decide +kernel
    rw [ha]
    exact (canonical9016 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA514 + difference 4 0) (sourceB514 + difference 0 4) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA514 + difference 4 0) (sourceB514 + difference 0 4) sourceC514) = raw9017 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9017; decide +kernel
    rw [ha]
    exact (canonical9017 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA514 + difference 5 0) (sourceB514 + difference 0 5) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1389) := by
    have ha : (tripleCharges (sourceA514 + difference 5 0) (sourceB514 + difference 0 5) sourceC514) = raw9018 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9018; decide +kernel
    rw [ha]
    exact (canonical9018 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA514 + sourceB514) sourceC514) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA514 + sourceB514) sourceC514) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA514 sourceB514 sourceC514 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA514 sourceB514 sourceC514
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm514, Integer.Sparse.eval]
  linarith only [hs]

def sourceA515 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB515 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC515 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm515 : Integer.Sparse Master := [(Sum.inr 1384, 1), (Sum.inr 2925, 2), (Sum.inr 3068, 1), (Sum.inr 3074, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

theorem sourceEq515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm515 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA515 + difference 1 0) (sourceB515 + difference 0 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1384) := by
    have ha : (tripleCharges (sourceA515 + difference 1 0) (sourceB515 + difference 0 1) sourceC515) = raw9014 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9014; decide +kernel
    rw [ha]
    exact (canonical9014 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA515 + difference 1 1) (sourceB515 + difference 1 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA515 + difference 1 1) (sourceB515 + difference 1 1) sourceC515) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA515 + difference 1 2) (sourceB515 + difference 2 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA515 + difference 1 2) (sourceB515 + difference 2 1) sourceC515) = raw9019 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9019; decide +kernel
    rw [ha]
    exact (canonical9019 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA515 + difference 1 3) (sourceB515 + difference 3 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA515 + difference 1 3) (sourceB515 + difference 3 1) sourceC515) = raw9020 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9020; decide +kernel
    rw [ha]
    exact (canonical9020 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA515 + difference 1 4) (sourceB515 + difference 4 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA515 + difference 1 4) (sourceB515 + difference 4 1) sourceC515) = raw9021 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9021; decide +kernel
    rw [ha]
    exact (canonical9021 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA515 + difference 1 5) (sourceB515 + difference 5 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA515 + difference 1 5) (sourceB515 + difference 5 1) sourceC515) = raw9022 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9022; decide +kernel
    rw [ha]
    exact (canonical9022 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA515 + sourceB515) sourceC515) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA515 + sourceB515) sourceC515) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA515 sourceB515 sourceC515 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA515 sourceB515 sourceC515
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm515, Integer.Sparse.eval]
  linarith only [hs]

def sourceA516 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB516 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC516 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm516 : Integer.Sparse Master := [(Sum.inr 2857, 1), (Sum.inr 2981, 1), (Sum.inr 2985, 2), (Sum.inr 3078, 1), (Sum.inr 3953, 1), (Sum.inr 4091, -1)]

theorem sourceEq516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm516 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA516 + difference 0 1) (sourceB516 + difference 1 0) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA516 + difference 0 1) (sourceB516 + difference 1 0) sourceC516) = raw9008 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9008; decide +kernel
    rw [ha]
    exact (canonical9008 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA516 + difference 1 1) (sourceB516 + difference 1 1) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA516 + difference 1 1) (sourceB516 + difference 1 1) sourceC516) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA516 + difference 2 1) (sourceB516 + difference 1 2) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2985) := by
    have ha : (tripleCharges (sourceA516 + difference 2 1) (sourceB516 + difference 1 2) sourceC516) = raw9023 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9023; decide +kernel
    rw [ha]
    exact (canonical9023 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA516 + difference 3 1) (sourceB516 + difference 1 3) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2985) := by
    have ha : (tripleCharges (sourceA516 + difference 3 1) (sourceB516 + difference 1 3) sourceC516) = raw9024 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9024; decide +kernel
    rw [ha]
    exact (canonical9024 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA516 + difference 4 1) (sourceB516 + difference 1 4) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA516 + difference 4 1) (sourceB516 + difference 1 4) sourceC516) = raw9025 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9025; decide +kernel
    rw [ha]
    exact (canonical9025 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA516 + difference 5 1) (sourceB516 + difference 1 5) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2857) := by
    have ha : (tripleCharges (sourceA516 + difference 5 1) (sourceB516 + difference 1 5) sourceC516) = raw9026 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9026; decide +kernel
    rw [ha]
    exact (canonical9026 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA516 + sourceB516) sourceC516) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA516 + sourceB516) sourceC516) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA516 sourceB516 sourceC516 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA516 sourceB516 sourceC516
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm516, Integer.Sparse.eval]
  linarith only [hs]

def sourceA517 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB517 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC517 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm517 : Integer.Sparse Master := [(Sum.inr 1407, 1), (Sum.inr 2955, 1), (Sum.inr 2985, 1), (Sum.inr 3078, 1), (Sum.inr 3092, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

theorem sourceEq517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm517 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA517 + difference 2 0) (sourceB517 + difference 0 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1407) := by
    have ha : (tripleCharges (sourceA517 + difference 2 0) (sourceB517 + difference 0 2) sourceC517) = raw9015 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9015; decide +kernel
    rw [ha]
    exact (canonical9015 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA517 + difference 2 1) (sourceB517 + difference 1 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2985) := by
    have ha : (tripleCharges (sourceA517 + difference 2 1) (sourceB517 + difference 1 2) sourceC517) = raw9023 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9023; decide +kernel
    rw [ha]
    exact (canonical9023 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA517 + difference 2 2) (sourceB517 + difference 2 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA517 + difference 2 2) (sourceB517 + difference 2 2) sourceC517) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA517 + difference 2 3) (sourceB517 + difference 3 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA517 + difference 2 3) (sourceB517 + difference 3 2) sourceC517) = raw9027 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9027; decide +kernel
    rw [ha]
    exact (canonical9027 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA517 + difference 2 4) (sourceB517 + difference 4 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA517 + difference 2 4) (sourceB517 + difference 4 2) sourceC517) = raw9028 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9028; decide +kernel
    rw [ha]
    exact (canonical9028 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA517 + difference 2 5) (sourceB517 + difference 5 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA517 + difference 2 5) (sourceB517 + difference 5 2) sourceC517) = raw9029 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9029; decide +kernel
    rw [ha]
    exact (canonical9029 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA517 + sourceB517) sourceC517) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA517 + sourceB517) sourceC517) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA517 sourceB517 sourceC517 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA517 sourceB517 sourceC517
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm517, Integer.Sparse.eval]
  linarith only [hs]

def sourceA518 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB518 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC518 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm518 : Integer.Sparse Master := [(Sum.inr 2865, 1), (Sum.inr 2925, 1), (Sum.inr 2931, 1), (Sum.inr 2955, 1), (Sum.inr 3078, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

theorem sourceEq518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm518 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA518 + difference 0 2) (sourceB518 + difference 2 0) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA518 + difference 0 2) (sourceB518 + difference 2 0) sourceC518) = raw9009 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9009; decide +kernel
    rw [ha]
    exact (canonical9009 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA518 + difference 1 2) (sourceB518 + difference 2 1) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA518 + difference 1 2) (sourceB518 + difference 2 1) sourceC518) = raw9019 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9019; decide +kernel
    rw [ha]
    exact (canonical9019 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA518 + difference 2 2) (sourceB518 + difference 2 2) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA518 + difference 2 2) (sourceB518 + difference 2 2) sourceC518) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA518 + difference 3 2) (sourceB518 + difference 2 3) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA518 + difference 3 2) (sourceB518 + difference 2 3) sourceC518) = raw9030 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9030; decide +kernel
    rw [ha]
    exact (canonical9030 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA518 + difference 4 2) (sourceB518 + difference 2 4) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA518 + difference 4 2) (sourceB518 + difference 2 4) sourceC518) = raw9031 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9031; decide +kernel
    rw [ha]
    exact (canonical9031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA518 + difference 5 2) (sourceB518 + difference 2 5) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA518 + difference 5 2) (sourceB518 + difference 2 5) sourceC518) = raw9032 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9032; decide +kernel
    rw [ha]
    exact (canonical9032 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA518 + sourceB518) sourceC518) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA518 + sourceB518) sourceC518) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA518 sourceB518 sourceC518 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA518 sourceB518 sourceC518
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm518, Integer.Sparse.eval]
  linarith only [hs]

def sourceA519 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB519 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC519 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm519 : Integer.Sparse Master := [(Sum.inr 1391, 1), (Sum.inr 2931, 2), (Sum.inr 2981, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

theorem sourceEq519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm519 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA519 + difference 4 0) (sourceB519 + difference 0 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA519 + difference 4 0) (sourceB519 + difference 0 4) sourceC519) = raw9017 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9017; decide +kernel
    rw [ha]
    exact (canonical9017 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA519 + difference 4 1) (sourceB519 + difference 1 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA519 + difference 4 1) (sourceB519 + difference 1 4) sourceC519) = raw9025 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9025; decide +kernel
    rw [ha]
    exact (canonical9025 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA519 + difference 4 2) (sourceB519 + difference 2 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA519 + difference 4 2) (sourceB519 + difference 2 4) sourceC519) = raw9031 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9031; decide +kernel
    rw [ha]
    exact (canonical9031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA519 + difference 4 3) (sourceB519 + difference 3 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA519 + difference 4 3) (sourceB519 + difference 3 4) sourceC519) = raw9033 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9033; decide +kernel
    rw [ha]
    exact (canonical9033 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA519 + difference 4 4) (sourceB519 + difference 4 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA519 + difference 4 4) (sourceB519 + difference 4 4) sourceC519) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA519 + difference 4 5) (sourceB519 + difference 5 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA519 + difference 4 5) (sourceB519 + difference 5 4) sourceC519) = raw9034 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9034; decide +kernel
    rw [ha]
    exact (canonical9034 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA519 + sourceB519) sourceC519) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA519 + sourceB519) sourceC519) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA519 sourceB519 sourceC519 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA519 sourceB519 sourceC519
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm519, Integer.Sparse.eval]
  linarith only [hs]

def sourceA520 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB520 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC520 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm520 : Integer.Sparse Master := [(Sum.inr 3031, 1), (Sum.inr 3068, 1), (Sum.inr 3078, 1), (Sum.inr 3092, 2), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

theorem sourceEq520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm520 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA520 + difference 0 4) (sourceB520 + difference 4 0) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA520 + difference 0 4) (sourceB520 + difference 4 0) sourceC520) = raw9011 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9011; decide +kernel
    rw [ha]
    exact (canonical9011 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA520 + difference 1 4) (sourceB520 + difference 4 1) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA520 + difference 1 4) (sourceB520 + difference 4 1) sourceC520) = raw9021 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9021; decide +kernel
    rw [ha]
    exact (canonical9021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA520 + difference 2 4) (sourceB520 + difference 4 2) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA520 + difference 2 4) (sourceB520 + difference 4 2) sourceC520) = raw9028 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9028; decide +kernel
    rw [ha]
    exact (canonical9028 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA520 + difference 3 4) (sourceB520 + difference 4 3) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA520 + difference 3 4) (sourceB520 + difference 4 3) sourceC520) = raw9035 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9035; decide +kernel
    rw [ha]
    exact (canonical9035 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA520 + difference 4 4) (sourceB520 + difference 4 4) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA520 + difference 4 4) (sourceB520 + difference 4 4) sourceC520) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA520 + difference 5 4) (sourceB520 + difference 4 5) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA520 + difference 5 4) (sourceB520 + difference 4 5) sourceC520) = raw9036 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9036; decide +kernel
    rw [ha]
    exact (canonical9036 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA520 + sourceB520) sourceC520) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA520 + sourceB520) sourceC520) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA520 sourceB520 sourceC520 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA520 sourceB520 sourceC520
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm520, Integer.Sparse.eval]
  linarith only [hs]

def sourceA521 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB521 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC521 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm521 : Integer.Sparse Master := [(Sum.inr 1389, 1), (Sum.inr 2857, 1), (Sum.inr 2865, 2), (Sum.inr 3031, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

theorem sourceEq521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm521 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA521 + difference 5 0) (sourceB521 + difference 0 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1389) := by
    have ha : (tripleCharges (sourceA521 + difference 5 0) (sourceB521 + difference 0 5) sourceC521) = raw9018 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9018; decide +kernel
    rw [ha]
    exact (canonical9018 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA521 + difference 5 1) (sourceB521 + difference 1 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2857) := by
    have ha : (tripleCharges (sourceA521 + difference 5 1) (sourceB521 + difference 1 5) sourceC521) = raw9026 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9026; decide +kernel
    rw [ha]
    exact (canonical9026 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA521 + difference 5 2) (sourceB521 + difference 2 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA521 + difference 5 2) (sourceB521 + difference 2 5) sourceC521) = raw9032 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9032; decide +kernel
    rw [ha]
    exact (canonical9032 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA521 + difference 5 3) (sourceB521 + difference 3 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA521 + difference 5 3) (sourceB521 + difference 3 5) sourceC521) = raw9037 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9037; decide +kernel
    rw [ha]
    exact (canonical9037 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA521 + difference 5 4) (sourceB521 + difference 4 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA521 + difference 5 4) (sourceB521 + difference 4 5) sourceC521) = raw9036 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9036; decide +kernel
    rw [ha]
    exact (canonical9036 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA521 + difference 5 5) (sourceB521 + difference 5 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA521 + difference 5 5) (sourceB521 + difference 5 5) sourceC521) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA521 + sourceB521) sourceC521) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA521 + sourceB521) sourceC521) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA521 sourceB521 sourceC521 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA521 sourceB521 sourceC521
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm521, Integer.Sparse.eval]
  linarith only [hs]

def sourceA522 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB522 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC522 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm522 : Integer.Sparse Master := [(Sum.inr 4863, 1), (Sum.inr 4865, 1), (Sum.inr 4867, 2), (Sum.inr 4888, 1), (Sum.inr 5194, 1), (Sum.inr 5195, 2), (Sum.inr 5205, 1), (Sum.inr 5242, 1), (Sum.inr 5248, 1), (Sum.inr 5249, 1), (Sum.inr 5250, 1), (Sum.inr 5253, 2), (Sum.inr 5275, 2), (Sum.inr 5277, 1), (Sum.inr 5279, 1), (Sum.inr 5282, 2), (Sum.inr 5284, 1), (Sum.inr 5287, 2), (Sum.inr 5291, 2), (Sum.inr 5293, 2), (Sum.inr 5300, 2)]

theorem sourceEq522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm522 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA522 + difference 0 1) (sourceB522 + difference 1 0) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5242) := by
    have ha : (tripleCharges (sourceA522 + difference 0 1) (sourceB522 + difference 1 0) sourceC522) = raw7223 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw7223; decide +kernel
    rw [ha]
    exact (canonical7223 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA522 + difference 0 2) (sourceB522 + difference 2 0) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA522 + difference 0 2) (sourceB522 + difference 2 0) sourceC522) = raw7920 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw7920; decide +kernel
    rw [ha]
    exact (canonical7920 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA522 + difference 0 3) (sourceB522 + difference 3 0) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA522 + difference 0 3) (sourceB522 + difference 3 0) sourceC522) = raw9038 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9038; decide +kernel
    rw [ha]
    exact (canonical9038 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA522 + difference 0 4) (sourceB522 + difference 4 0) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA522 + difference 0 4) (sourceB522 + difference 4 0) sourceC522) = raw9039 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9039; decide +kernel
    rw [ha]
    exact (canonical9039 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA522 + difference 0 5) (sourceB522 + difference 5 0) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA522 + difference 0 5) (sourceB522 + difference 5 0) sourceC522) = raw9040 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9040; decide +kernel
    rw [ha]
    exact (canonical9040 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA522 + difference 1 0) (sourceB522 + difference 0 1) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA522 + difference 1 0) (sourceB522 + difference 0 1) sourceC522) = raw5687 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw5687; decide +kernel
    rw [ha]
    exact (canonical5687 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA522 + difference 1 2) (sourceB522 + difference 2 1) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA522 + difference 1 2) (sourceB522 + difference 2 1) sourceC522) = raw7924 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw7924; decide +kernel
    rw [ha]
    exact (canonical7924 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA522 + difference 1 3) (sourceB522 + difference 3 1) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA522 + difference 1 3) (sourceB522 + difference 3 1) sourceC522) = raw9041 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9041; decide +kernel
    rw [ha]
    exact (canonical9041 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA522 + difference 1 4) (sourceB522 + difference 4 1) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5194) := by
    have ha : (tripleCharges (sourceA522 + difference 1 4) (sourceB522 + difference 4 1) sourceC522) = raw9042 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9042; decide +kernel
    rw [ha]
    exact (canonical9042 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA522 + difference 1 5) (sourceB522 + difference 5 1) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5277) := by
    have ha : (tripleCharges (sourceA522 + difference 1 5) (sourceB522 + difference 5 1) sourceC522) = raw5661 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw5661; decide +kernel
    rw [ha]
    exact (canonical5661 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA522 + difference 2 0) (sourceB522 + difference 0 2) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA522 + difference 2 0) (sourceB522 + difference 0 2) sourceC522) = raw9043 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9043; decide +kernel
    rw [ha]
    exact (canonical9043 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA522 + difference 2 1) (sourceB522 + difference 1 2) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5253) := by
    have ha : (tripleCharges (sourceA522 + difference 2 1) (sourceB522 + difference 1 2) sourceC522) = raw7230 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw7230; decide +kernel
    rw [ha]
    exact (canonical7230 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA522 + difference 2 3) (sourceB522 + difference 3 2) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA522 + difference 2 3) (sourceB522 + difference 3 2) sourceC522) = raw9044 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9044; decide +kernel
    rw [ha]
    exact (canonical9044 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA522 + difference 2 4) (sourceB522 + difference 4 2) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5195) := by
    have ha : (tripleCharges (sourceA522 + difference 2 4) (sourceB522 + difference 4 2) sourceC522) = raw9045 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9045; decide +kernel
    rw [ha]
    exact (canonical9045 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA522 + difference 2 5) (sourceB522 + difference 5 2) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA522 + difference 2 5) (sourceB522 + difference 5 2) sourceC522) = raw9046 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9046; decide +kernel
    rw [ha]
    exact (canonical9046 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA522 + difference 3 0) (sourceB522 + difference 0 3) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA522 + difference 3 0) (sourceB522 + difference 0 3) sourceC522) = raw8560 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw8560; decide +kernel
    rw [ha]
    exact (canonical8560 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA522 + difference 3 1) (sourceB522 + difference 1 3) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5253) := by
    have ha : (tripleCharges (sourceA522 + difference 3 1) (sourceB522 + difference 1 3) sourceC522) = raw6713 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw6713; decide +kernel
    rw [ha]
    exact (canonical6713 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA522 + difference 3 2) (sourceB522 + difference 2 3) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA522 + difference 3 2) (sourceB522 + difference 2 3) sourceC522) = raw6708 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw6708; decide +kernel
    rw [ha]
    exact (canonical6708 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA522 + difference 3 4) (sourceB522 + difference 4 3) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5195) := by
    have ha : (tripleCharges (sourceA522 + difference 3 4) (sourceB522 + difference 4 3) sourceC522) = raw8561 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw8561; decide +kernel
    rw [ha]
    exact (canonical8561 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA522 + difference 3 5) (sourceB522 + difference 5 3) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA522 + difference 3 5) (sourceB522 + difference 5 3) sourceC522) = raw8562 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw8562; decide +kernel
    rw [ha]
    exact (canonical8562 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA522 + difference 4 0) (sourceB522 + difference 0 4) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA522 + difference 4 0) (sourceB522 + difference 0 4) sourceC522) = raw5684 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw5684; decide +kernel
    rw [ha]
    exact (canonical5684 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA522 + difference 4 1) (sourceB522 + difference 1 4) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA522 + difference 4 1) (sourceB522 + difference 1 4) sourceC522) = raw6712 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw6712; decide +kernel
    rw [ha]
    exact (canonical6712 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA522 + difference 4 2) (sourceB522 + difference 2 4) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA522 + difference 4 2) (sourceB522 + difference 2 4) sourceC522) = raw6707 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw6707; decide +kernel
    rw [ha]
    exact (canonical6707 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA522 + difference 4 3) (sourceB522 + difference 3 4) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA522 + difference 4 3) (sourceB522 + difference 3 4) sourceC522) = raw7225 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw7225; decide +kernel
    rw [ha]
    exact (canonical7225 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA522 + difference 4 5) (sourceB522 + difference 5 4) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA522 + difference 4 5) (sourceB522 + difference 5 4) sourceC522) = raw5658 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw5658; decide +kernel
    rw [ha]
    exact (canonical5658 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA522 + difference 5 0) (sourceB522 + difference 0 5) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA522 + difference 5 0) (sourceB522 + difference 0 5) sourceC522) = raw9047 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9047; decide +kernel
    rw [ha]
    exact (canonical9047 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA522 + difference 5 1) (sourceB522 + difference 1 5) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA522 + difference 5 1) (sourceB522 + difference 1 5) sourceC522) = raw7238 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw7238; decide +kernel
    rw [ha]
    exact (canonical7238 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA522 + difference 5 2) (sourceB522 + difference 2 5) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA522 + difference 5 2) (sourceB522 + difference 2 5) sourceC522) = raw7930 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw7930; decide +kernel
    rw [ha]
    exact (canonical7930 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA522 + difference 5 3) (sourceB522 + difference 3 5) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA522 + difference 5 3) (sourceB522 + difference 3 5) sourceC522) = raw9048 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9048; decide +kernel
    rw [ha]
    exact (canonical9048 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA522 + difference 5 4) (sourceB522 + difference 4 5) sourceC522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA522 + difference 5 4) (sourceB522 + difference 4 5) sourceC522) = raw9049 := by
      apply Matrix.ext; unfold tripleCharges sourceA522 sourceB522 sourceC522 difference raw9049; decide +kernel
    rw [ha]
    exact (canonical9049 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA522 sourceB522 sourceC522
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm522, Integer.Sparse.eval]
  linarith only [hs]

def sourceA523 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB523 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC523 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm523 : Integer.Sparse Master := [(Sum.inr 2232, 1), (Sum.inr 2242, 1), (Sum.inr 2244, 1), (Sum.inr 2251, 2), (Sum.inr 2628, 1), (Sum.inr 2629, 2), (Sum.inr 2641, 1), (Sum.inr 2708, 1), (Sum.inr 2709, 1), (Sum.inr 2713, 2), (Sum.inr 2745, 1), (Sum.inr 2748, 1), (Sum.inr 2751, 2), (Sum.inr 2753, 1), (Sum.inr 2758, 2), (Sum.inr 2765, 2), (Sum.inr 2767, 2), (Sum.inr 2774, 2), (Sum.inr 3080, 1), (Sum.inr 3106, 1), (Sum.inr 3110, 2)]

theorem sourceEq523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm523 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA523 + difference 0 1) (sourceB523 + difference 1 0) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3080) := by
    have ha : (tripleCharges (sourceA523 + difference 0 1) (sourceB523 + difference 1 0) sourceC523) = raw7241 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw7241; decide +kernel
    rw [ha]
    exact (canonical7241 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA523 + difference 0 2) (sourceB523 + difference 2 0) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA523 + difference 0 2) (sourceB523 + difference 2 0) sourceC523) = raw7933 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw7933; decide +kernel
    rw [ha]
    exact (canonical7933 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA523 + difference 0 3) (sourceB523 + difference 3 0) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA523 + difference 0 3) (sourceB523 + difference 3 0) sourceC523) = raw9050 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9050; decide +kernel
    rw [ha]
    exact (canonical9050 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA523 + difference 0 4) (sourceB523 + difference 4 0) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2641) := by
    have ha : (tripleCharges (sourceA523 + difference 0 4) (sourceB523 + difference 4 0) sourceC523) = raw9051 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9051; decide +kernel
    rw [ha]
    exact (canonical9051 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA523 + difference 0 5) (sourceB523 + difference 5 0) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3106) := by
    have ha : (tripleCharges (sourceA523 + difference 0 5) (sourceB523 + difference 5 0) sourceC523) = raw9052 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9052; decide +kernel
    rw [ha]
    exact (canonical9052 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA523 + difference 1 0) (sourceB523 + difference 0 1) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA523 + difference 1 0) (sourceB523 + difference 0 1) sourceC523) = raw5717 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw5717; decide +kernel
    rw [ha]
    exact (canonical5717 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA523 + difference 1 2) (sourceB523 + difference 2 1) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA523 + difference 1 2) (sourceB523 + difference 2 1) sourceC523) = raw7937 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw7937; decide +kernel
    rw [ha]
    exact (canonical7937 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA523 + difference 1 3) (sourceB523 + difference 3 1) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA523 + difference 1 3) (sourceB523 + difference 3 1) sourceC523) = raw9053 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9053; decide +kernel
    rw [ha]
    exact (canonical9053 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA523 + difference 1 4) (sourceB523 + difference 4 1) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2628) := by
    have ha : (tripleCharges (sourceA523 + difference 1 4) (sourceB523 + difference 4 1) sourceC523) = raw9054 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9054; decide +kernel
    rw [ha]
    exact (canonical9054 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA523 + difference 1 5) (sourceB523 + difference 5 1) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2745) := by
    have ha : (tripleCharges (sourceA523 + difference 1 5) (sourceB523 + difference 5 1) sourceC523) = raw5691 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw5691; decide +kernel
    rw [ha]
    exact (canonical5691 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA523 + difference 2 0) (sourceB523 + difference 0 2) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA523 + difference 2 0) (sourceB523 + difference 0 2) sourceC523) = raw9055 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9055; decide +kernel
    rw [ha]
    exact (canonical9055 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA523 + difference 2 1) (sourceB523 + difference 1 2) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2713) := by
    have ha : (tripleCharges (sourceA523 + difference 2 1) (sourceB523 + difference 1 2) sourceC523) = raw7248 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw7248; decide +kernel
    rw [ha]
    exact (canonical7248 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA523 + difference 2 3) (sourceB523 + difference 3 2) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA523 + difference 2 3) (sourceB523 + difference 3 2) sourceC523) = raw9056 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9056; decide +kernel
    rw [ha]
    exact (canonical9056 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA523 + difference 2 4) (sourceB523 + difference 4 2) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2629) := by
    have ha : (tripleCharges (sourceA523 + difference 2 4) (sourceB523 + difference 4 2) sourceC523) = raw9057 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9057; decide +kernel
    rw [ha]
    exact (canonical9057 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA523 + difference 2 5) (sourceB523 + difference 5 2) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA523 + difference 2 5) (sourceB523 + difference 5 2) sourceC523) = raw9058 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9058; decide +kernel
    rw [ha]
    exact (canonical9058 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA523 + difference 3 0) (sourceB523 + difference 0 3) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA523 + difference 3 0) (sourceB523 + difference 0 3) sourceC523) = raw8577 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw8577; decide +kernel
    rw [ha]
    exact (canonical8577 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA523 + difference 3 1) (sourceB523 + difference 1 3) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2713) := by
    have ha : (tripleCharges (sourceA523 + difference 3 1) (sourceB523 + difference 1 3) sourceC523) = raw6741 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw6741; decide +kernel
    rw [ha]
    exact (canonical6741 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA523 + difference 3 2) (sourceB523 + difference 2 3) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA523 + difference 3 2) (sourceB523 + difference 2 3) sourceC523) = raw6736 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw6736; decide +kernel
    rw [ha]
    exact (canonical6736 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA523 + difference 3 4) (sourceB523 + difference 4 3) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2629) := by
    have ha : (tripleCharges (sourceA523 + difference 3 4) (sourceB523 + difference 4 3) sourceC523) = raw8578 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw8578; decide +kernel
    rw [ha]
    exact (canonical8578 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA523 + difference 3 5) (sourceB523 + difference 5 3) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA523 + difference 3 5) (sourceB523 + difference 5 3) sourceC523) = raw8579 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw8579; decide +kernel
    rw [ha]
    exact (canonical8579 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA523 + difference 4 0) (sourceB523 + difference 0 4) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA523 + difference 4 0) (sourceB523 + difference 0 4) sourceC523) = raw5714 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw5714; decide +kernel
    rw [ha]
    exact (canonical5714 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA523 + difference 4 1) (sourceB523 + difference 1 4) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA523 + difference 4 1) (sourceB523 + difference 1 4) sourceC523) = raw6740 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw6740; decide +kernel
    rw [ha]
    exact (canonical6740 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA523 + difference 4 2) (sourceB523 + difference 2 4) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA523 + difference 4 2) (sourceB523 + difference 2 4) sourceC523) = raw6735 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw6735; decide +kernel
    rw [ha]
    exact (canonical6735 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA523 + difference 4 3) (sourceB523 + difference 3 4) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA523 + difference 4 3) (sourceB523 + difference 3 4) sourceC523) = raw7243 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw7243; decide +kernel
    rw [ha]
    exact (canonical7243 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA523 + difference 4 5) (sourceB523 + difference 5 4) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA523 + difference 4 5) (sourceB523 + difference 5 4) sourceC523) = raw5688 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw5688; decide +kernel
    rw [ha]
    exact (canonical5688 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA523 + difference 5 0) (sourceB523 + difference 0 5) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA523 + difference 5 0) (sourceB523 + difference 0 5) sourceC523) = raw9059 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9059; decide +kernel
    rw [ha]
    exact (canonical9059 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA523 + difference 5 1) (sourceB523 + difference 1 5) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA523 + difference 5 1) (sourceB523 + difference 1 5) sourceC523) = raw7256 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw7256; decide +kernel
    rw [ha]
    exact (canonical7256 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA523 + difference 5 2) (sourceB523 + difference 2 5) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA523 + difference 5 2) (sourceB523 + difference 2 5) sourceC523) = raw7943 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw7943; decide +kernel
    rw [ha]
    exact (canonical7943 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA523 + difference 5 3) (sourceB523 + difference 3 5) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA523 + difference 5 3) (sourceB523 + difference 3 5) sourceC523) = raw9060 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9060; decide +kernel
    rw [ha]
    exact (canonical9060 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA523 + difference 5 4) (sourceB523 + difference 4 5) sourceC523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA523 + difference 5 4) (sourceB523 + difference 4 5) sourceC523) = raw9061 := by
      apply Matrix.ext; unfold tripleCharges sourceA523 sourceB523 sourceC523 difference raw9061; decide +kernel
    rw [ha]
    exact (canonical9061 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA523 sourceB523 sourceC523
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm523, Integer.Sparse.eval]
  linarith only [hs]

def sourceA524 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB524 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC524 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm524 : Integer.Sparse Master := [(Sum.inr 2695, 1), (Sum.inr 2705, 1), (Sum.inr 2706, 1), (Sum.inr 2743, 2), (Sum.inr 3017, 2), (Sum.inr 3025, 2), (Sum.inr 3026, 2), (Sum.inr 3055, 2), (Sum.inr 3059, 1), (Sum.inr 3060, 1), (Sum.inr 3065, 1), (Sum.inr 3066, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 2), (Sum.inr 3079, 1), (Sum.inr 3102, 2), (Sum.inr 3103, 2), (Sum.inr 3179, 1), (Sum.inr 3180, 2), (Sum.inr 3185, 1), (Sum.inr 3227, 1)]

theorem sourceEq524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm524 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA524 + difference 0 1) (sourceB524 + difference 1 0) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA524 + difference 0 1) (sourceB524 + difference 1 0) sourceC524) = raw7259 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw7259; decide +kernel
    rw [ha]
    exact (canonical7259 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA524 + difference 0 2) (sourceB524 + difference 2 0) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA524 + difference 0 2) (sourceB524 + difference 2 0) sourceC524) = raw7946 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw7946; decide +kernel
    rw [ha]
    exact (canonical7946 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA524 + difference 0 3) (sourceB524 + difference 3 0) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA524 + difference 0 3) (sourceB524 + difference 3 0) sourceC524) = raw9062 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9062; decide +kernel
    rw [ha]
    exact (canonical9062 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA524 + difference 0 4) (sourceB524 + difference 4 0) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA524 + difference 0 4) (sourceB524 + difference 4 0) sourceC524) = raw9063 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9063; decide +kernel
    rw [ha]
    exact (canonical9063 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA524 + difference 0 5) (sourceB524 + difference 5 0) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA524 + difference 0 5) (sourceB524 + difference 5 0) sourceC524) = raw9064 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9064; decide +kernel
    rw [ha]
    exact (canonical9064 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA524 + difference 1 0) (sourceB524 + difference 0 1) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3179) := by
    have ha : (tripleCharges (sourceA524 + difference 1 0) (sourceB524 + difference 0 1) sourceC524) = raw5747 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw5747; decide +kernel
    rw [ha]
    exact (canonical5747 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA524 + difference 1 2) (sourceB524 + difference 2 1) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA524 + difference 1 2) (sourceB524 + difference 2 1) sourceC524) = raw7950 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw7950; decide +kernel
    rw [ha]
    exact (canonical7950 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA524 + difference 1 3) (sourceB524 + difference 3 1) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA524 + difference 1 3) (sourceB524 + difference 3 1) sourceC524) = raw9065 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9065; decide +kernel
    rw [ha]
    exact (canonical9065 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA524 + difference 1 4) (sourceB524 + difference 4 1) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3060) := by
    have ha : (tripleCharges (sourceA524 + difference 1 4) (sourceB524 + difference 4 1) sourceC524) = raw9066 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9066; decide +kernel
    rw [ha]
    exact (canonical9066 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA524 + difference 1 5) (sourceB524 + difference 5 1) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA524 + difference 1 5) (sourceB524 + difference 5 1) sourceC524) = raw5721 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw5721; decide +kernel
    rw [ha]
    exact (canonical5721 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA524 + difference 2 0) (sourceB524 + difference 0 2) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA524 + difference 2 0) (sourceB524 + difference 0 2) sourceC524) = raw9067 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9067; decide +kernel
    rw [ha]
    exact (canonical9067 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA524 + difference 2 1) (sourceB524 + difference 1 2) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3017) := by
    have ha : (tripleCharges (sourceA524 + difference 2 1) (sourceB524 + difference 1 2) sourceC524) = raw7266 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw7266; decide +kernel
    rw [ha]
    exact (canonical7266 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA524 + difference 2 3) (sourceB524 + difference 3 2) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA524 + difference 2 3) (sourceB524 + difference 3 2) sourceC524) = raw9068 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9068; decide +kernel
    rw [ha]
    exact (canonical9068 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA524 + difference 2 4) (sourceB524 + difference 4 2) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3026) := by
    have ha : (tripleCharges (sourceA524 + difference 2 4) (sourceB524 + difference 4 2) sourceC524) = raw9069 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9069; decide +kernel
    rw [ha]
    exact (canonical9069 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA524 + difference 2 5) (sourceB524 + difference 5 2) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA524 + difference 2 5) (sourceB524 + difference 5 2) sourceC524) = raw9070 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9070; decide +kernel
    rw [ha]
    exact (canonical9070 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA524 + difference 3 0) (sourceB524 + difference 0 3) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA524 + difference 3 0) (sourceB524 + difference 0 3) sourceC524) = raw8594 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw8594; decide +kernel
    rw [ha]
    exact (canonical8594 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA524 + difference 3 1) (sourceB524 + difference 1 3) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3017) := by
    have ha : (tripleCharges (sourceA524 + difference 3 1) (sourceB524 + difference 1 3) sourceC524) = raw6769 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw6769; decide +kernel
    rw [ha]
    exact (canonical6769 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA524 + difference 3 2) (sourceB524 + difference 2 3) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA524 + difference 3 2) (sourceB524 + difference 2 3) sourceC524) = raw6764 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw6764; decide +kernel
    rw [ha]
    exact (canonical6764 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA524 + difference 3 4) (sourceB524 + difference 4 3) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3026) := by
    have ha : (tripleCharges (sourceA524 + difference 3 4) (sourceB524 + difference 4 3) sourceC524) = raw8595 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw8595; decide +kernel
    rw [ha]
    exact (canonical8595 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA524 + difference 3 5) (sourceB524 + difference 5 3) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA524 + difference 3 5) (sourceB524 + difference 5 3) sourceC524) = raw8596 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw8596; decide +kernel
    rw [ha]
    exact (canonical8596 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA524 + difference 4 0) (sourceB524 + difference 0 4) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA524 + difference 4 0) (sourceB524 + difference 0 4) sourceC524) = raw5744 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw5744; decide +kernel
    rw [ha]
    exact (canonical5744 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA524 + difference 4 1) (sourceB524 + difference 1 4) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA524 + difference 4 1) (sourceB524 + difference 1 4) sourceC524) = raw6768 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw6768; decide +kernel
    rw [ha]
    exact (canonical6768 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA524 + difference 4 2) (sourceB524 + difference 2 4) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA524 + difference 4 2) (sourceB524 + difference 2 4) sourceC524) = raw6763 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw6763; decide +kernel
    rw [ha]
    exact (canonical6763 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA524 + difference 4 3) (sourceB524 + difference 3 4) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA524 + difference 4 3) (sourceB524 + difference 3 4) sourceC524) = raw7261 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw7261; decide +kernel
    rw [ha]
    exact (canonical7261 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA524 + difference 4 5) (sourceB524 + difference 5 4) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA524 + difference 4 5) (sourceB524 + difference 5 4) sourceC524) = raw5718 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw5718; decide +kernel
    rw [ha]
    exact (canonical5718 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA524 + difference 5 0) (sourceB524 + difference 0 5) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA524 + difference 5 0) (sourceB524 + difference 0 5) sourceC524) = raw9071 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9071; decide +kernel
    rw [ha]
    exact (canonical9071 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA524 + difference 5 1) (sourceB524 + difference 1 5) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA524 + difference 5 1) (sourceB524 + difference 1 5) sourceC524) = raw7274 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw7274; decide +kernel
    rw [ha]
    exact (canonical7274 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA524 + difference 5 2) (sourceB524 + difference 2 5) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA524 + difference 5 2) (sourceB524 + difference 2 5) sourceC524) = raw7956 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw7956; decide +kernel
    rw [ha]
    exact (canonical7956 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA524 + difference 5 3) (sourceB524 + difference 3 5) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA524 + difference 5 3) (sourceB524 + difference 3 5) sourceC524) = raw9072 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9072; decide +kernel
    rw [ha]
    exact (canonical9072 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA524 + difference 5 4) (sourceB524 + difference 4 5) sourceC524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA524 + difference 5 4) (sourceB524 + difference 4 5) sourceC524) = raw9073 := by
      apply Matrix.ext; unfold tripleCharges sourceA524 sourceB524 sourceC524 difference raw9073; decide +kernel
    rw [ha]
    exact (canonical9073 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA524 sourceB524 sourceC524
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm524, Integer.Sparse.eval]
  linarith only [hs]

def sourceA525 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB525 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC525 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm525 : Integer.Sparse Master := [(Sum.inr 2879, 1), (Sum.inr 3494, 1), (Sum.inr 3498, 1), (Sum.inr 3548, 2), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

theorem sourceEq525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm525 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA525 + difference 0 0) (sourceB525 + difference 0 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA525 + difference 0 0) (sourceB525 + difference 0 0) sourceC525) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA525 + difference 0 1) (sourceB525 + difference 1 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3494) := by
    have ha : (tripleCharges (sourceA525 + difference 0 1) (sourceB525 + difference 1 0) sourceC525) = raw7277 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw7277; decide +kernel
    rw [ha]
    exact (canonical7277 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA525 + difference 0 2) (sourceB525 + difference 2 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA525 + difference 0 2) (sourceB525 + difference 2 0) sourceC525) = raw7959 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw7959; decide +kernel
    rw [ha]
    exact (canonical7959 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA525 + difference 0 3) (sourceB525 + difference 3 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA525 + difference 0 3) (sourceB525 + difference 3 0) sourceC525) = raw9074 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw9074; decide +kernel
    rw [ha]
    exact (canonical9074 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA525 + difference 0 4) (sourceB525 + difference 4 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA525 + difference 0 4) (sourceB525 + difference 4 0) sourceC525) = raw9075 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw9075; decide +kernel
    rw [ha]
    exact (canonical9075 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA525 + difference 0 5) (sourceB525 + difference 5 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3498) := by
    have ha : (tripleCharges (sourceA525 + difference 0 5) (sourceB525 + difference 5 0) sourceC525) = raw9076 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw9076; decide +kernel
    rw [ha]
    exact (canonical9076 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA525 + sourceB525) sourceC525) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA525 + sourceB525) sourceC525) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA525 sourceB525 sourceC525 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA525 sourceB525 sourceC525
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm525, Integer.Sparse.eval]
  linarith only [hs]

def sourceA526 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB526 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC526 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm526 : Integer.Sparse Master := [(Sum.inr 2104, 1), (Sum.inr 2106, 1), (Sum.inr 2108, 2), (Sum.inr 2262, 1), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

theorem sourceEq526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm526 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA526 + difference 0 0) (sourceB526 + difference 0 0) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA526 + difference 0 0) (sourceB526 + difference 0 0) sourceC526) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA526 + difference 1 0) (sourceB526 + difference 0 1) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA526 + difference 1 0) (sourceB526 + difference 0 1) sourceC526) = raw5767 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw5767; decide +kernel
    rw [ha]
    exact (canonical5767 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA526 + difference 2 0) (sourceB526 + difference 0 2) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA526 + difference 2 0) (sourceB526 + difference 0 2) sourceC526) = raw9077 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw9077; decide +kernel
    rw [ha]
    exact (canonical9077 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA526 + difference 3 0) (sourceB526 + difference 0 3) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA526 + difference 3 0) (sourceB526 + difference 0 3) sourceC526) = raw8608 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw8608; decide +kernel
    rw [ha]
    exact (canonical8608 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA526 + difference 4 0) (sourceB526 + difference 0 4) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA526 + difference 4 0) (sourceB526 + difference 0 4) sourceC526) = raw5768 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw5768; decide +kernel
    rw [ha]
    exact (canonical5768 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA526 + difference 5 0) (sourceB526 + difference 0 5) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA526 + difference 5 0) (sourceB526 + difference 0 5) sourceC526) = raw9078 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw9078; decide +kernel
    rw [ha]
    exact (canonical9078 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA526 + sourceB526) sourceC526) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA526 + sourceB526) sourceC526) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA526 sourceB526 sourceC526 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA526 sourceB526 sourceC526
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm526, Integer.Sparse.eval]
  linarith only [hs]

def sourceA527 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB527 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC527 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm527 : Integer.Sparse Master := [(Sum.inr 2104, 1), (Sum.inr 2877, 1), (Sum.inr 3576, 1), (Sum.inr 3580, 3), (Sum.inr 4084, -1)]

theorem sourceEq527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm527 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA527 + difference 1 0) (sourceB527 + difference 0 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA527 + difference 1 0) (sourceB527 + difference 0 1) sourceC527) = raw5767 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw5767; decide +kernel
    rw [ha]
    exact (canonical5767 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA527 + difference 1 1) (sourceB527 + difference 1 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA527 + difference 1 1) (sourceB527 + difference 1 1) sourceC527) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA527 + difference 1 2) (sourceB527 + difference 2 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA527 + difference 1 2) (sourceB527 + difference 2 1) sourceC527) = raw7965 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw7965; decide +kernel
    rw [ha]
    exact (canonical7965 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA527 + difference 1 3) (sourceB527 + difference 3 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA527 + difference 1 3) (sourceB527 + difference 3 1) sourceC527) = raw9079 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw9079; decide +kernel
    rw [ha]
    exact (canonical9079 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA527 + difference 1 4) (sourceB527 + difference 4 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2877) := by
    have ha : (tripleCharges (sourceA527 + difference 1 4) (sourceB527 + difference 4 1) sourceC527) = raw9080 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw9080; decide +kernel
    rw [ha]
    exact (canonical9080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA527 + difference 1 5) (sourceB527 + difference 5 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3576) := by
    have ha : (tripleCharges (sourceA527 + difference 1 5) (sourceB527 + difference 5 1) sourceC527) = raw5752 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw5752; decide +kernel
    rw [ha]
    exact (canonical5752 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA527 + sourceB527) sourceC527) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA527 + sourceB527) sourceC527) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA527 sourceB527 sourceC527 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA527 sourceB527 sourceC527
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm527, Integer.Sparse.eval]
  linarith only [hs]

def sourceA528 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB528 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC528 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm528 : Integer.Sparse Master := [(Sum.inr 2877, 1), (Sum.inr 2879, 1), (Sum.inr 2883, 2), (Sum.inr 3050, 1), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

theorem sourceEq528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm528 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA528 + difference 0 4) (sourceB528 + difference 4 0) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA528 + difference 0 4) (sourceB528 + difference 4 0) sourceC528) = raw9075 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw9075; decide +kernel
    rw [ha]
    exact (canonical9075 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA528 + difference 1 4) (sourceB528 + difference 4 1) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2877) := by
    have ha : (tripleCharges (sourceA528 + difference 1 4) (sourceB528 + difference 4 1) sourceC528) = raw9080 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw9080; decide +kernel
    rw [ha]
    exact (canonical9080 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA528 + difference 2 4) (sourceB528 + difference 4 2) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2883) := by
    have ha : (tripleCharges (sourceA528 + difference 2 4) (sourceB528 + difference 4 2) sourceC528) = raw9081 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw9081; decide +kernel
    rw [ha]
    exact (canonical9081 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA528 + difference 3 4) (sourceB528 + difference 4 3) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2883) := by
    have ha : (tripleCharges (sourceA528 + difference 3 4) (sourceB528 + difference 4 3) sourceC528) = raw8617 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw8617; decide +kernel
    rw [ha]
    exact (canonical8617 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA528 + difference 4 4) (sourceB528 + difference 4 4) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA528 + difference 4 4) (sourceB528 + difference 4 4) sourceC528) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA528 + difference 5 4) (sourceB528 + difference 4 5) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA528 + difference 5 4) (sourceB528 + difference 4 5) sourceC528) = raw9082 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw9082; decide +kernel
    rw [ha]
    exact (canonical9082 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA528 + sourceB528) sourceC528) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA528 + sourceB528) sourceC528) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA528 sourceB528 sourceC528 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA528 sourceB528 sourceC528
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm528, Integer.Sparse.eval]
  linarith only [hs]

def sourceA529 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB529 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC529 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm529 : Integer.Sparse Master := [(Sum.inr 2106, 1), (Sum.inr 3050, 1), (Sum.inr 3502, 1), (Sum.inr 3580, 1), (Sum.inr 3582, 2), (Sum.inr 4084, -1)]

theorem sourceEq529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm529 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA529 + difference 5 0) (sourceB529 + difference 0 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA529 + difference 5 0) (sourceB529 + difference 0 5) sourceC529) = raw9078 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw9078; decide +kernel
    rw [ha]
    exact (canonical9078 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA529 + difference 5 1) (sourceB529 + difference 1 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA529 + difference 5 1) (sourceB529 + difference 1 5) sourceC529) = raw7289 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw7289; decide +kernel
    rw [ha]
    exact (canonical7289 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA529 + difference 5 2) (sourceB529 + difference 2 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA529 + difference 5 2) (sourceB529 + difference 2 5) sourceC529) = raw7966 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw7966; decide +kernel
    rw [ha]
    exact (canonical7966 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA529 + difference 5 3) (sourceB529 + difference 3 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA529 + difference 5 3) (sourceB529 + difference 3 5) sourceC529) = raw9083 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw9083; decide +kernel
    rw [ha]
    exact (canonical9083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA529 + difference 5 4) (sourceB529 + difference 4 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA529 + difference 5 4) (sourceB529 + difference 4 5) sourceC529) = raw9082 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw9082; decide +kernel
    rw [ha]
    exact (canonical9082 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA529 + difference 5 5) (sourceB529 + difference 5 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA529 + difference 5 5) (sourceB529 + difference 5 5) sourceC529) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA529 + sourceB529) sourceC529) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA529 + sourceB529) sourceC529) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA529 sourceB529 sourceC529 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA529 sourceB529 sourceC529
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm529, Integer.Sparse.eval]
  linarith only [hs]

def sourceA530 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB530 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC530 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceForm530 : Integer.Sparse Master := [(Sum.inr 4581, 1), (Sum.inr 4583, 1), (Sum.inr 4586, 1), (Sum.inr 4602, 2), (Sum.inr 4729, 1), (Sum.inr 4742, 2), (Sum.inr 4890, 1), (Sum.inr 5142, 1), (Sum.inr 5149, 2), (Sum.inr 5192, 2), (Sum.inr 5193, 2), (Sum.inr 5204, 2), (Sum.inr 5283, 1), (Sum.inr 5284, 2), (Sum.inr 5292, 2), (Sum.inr 5294, 2), (Sum.inr 5406, 1), (Sum.inr 5411, 2), (Sum.inr 5452, 1), (Sum.inr 5453, 1)]

theorem sourceEq530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm530 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA530 + difference 0 1) (sourceB530 + difference 1 0) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA530 + difference 0 1) (sourceB530 + difference 1 0) sourceC530) = raw2965 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw2965; decide +kernel
    rw [ha]
    exact (canonical2965 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA530 + difference 0 2) (sourceB530 + difference 2 0) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA530 + difference 0 2) (sourceB530 + difference 2 0) sourceC530) = raw2966 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw2966; decide +kernel
    rw [ha]
    exact (canonical2966 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA530 + difference 0 3) (sourceB530 + difference 3 0) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA530 + difference 0 3) (sourceB530 + difference 3 0) sourceC530) = raw2967 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw2967; decide +kernel
    rw [ha]
    exact (canonical2967 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA530 + difference 0 4) (sourceB530 + difference 4 0) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA530 + difference 0 4) (sourceB530 + difference 4 0) sourceC530) = raw2968 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw2968; decide +kernel
    rw [ha]
    exact (canonical2968 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA530 + difference 0 5) (sourceB530 + difference 5 0) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA530 + difference 0 5) (sourceB530 + difference 5 0) sourceC530) = raw9084 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9084; decide +kernel
    rw [ha]
    exact (canonical9084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA530 + difference 1 0) (sourceB530 + difference 0 1) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA530 + difference 1 0) (sourceB530 + difference 0 1) sourceC530) = raw9085 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9085; decide +kernel
    rw [ha]
    exact (canonical9085 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA530 + difference 1 2) (sourceB530 + difference 2 1) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA530 + difference 1 2) (sourceB530 + difference 2 1) sourceC530) = raw9086 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9086; decide +kernel
    rw [ha]
    exact (canonical9086 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA530 + difference 1 3) (sourceB530 + difference 3 1) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA530 + difference 1 3) (sourceB530 + difference 3 1) sourceC530) = raw9087 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9087; decide +kernel
    rw [ha]
    exact (canonical9087 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA530 + difference 1 4) (sourceB530 + difference 4 1) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA530 + difference 1 4) (sourceB530 + difference 4 1) sourceC530) = raw9088 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9088; decide +kernel
    rw [ha]
    exact (canonical9088 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA530 + difference 1 5) (sourceB530 + difference 5 1) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA530 + difference 1 5) (sourceB530 + difference 5 1) sourceC530) = raw2944 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw2944; decide +kernel
    rw [ha]
    exact (canonical2944 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA530 + difference 2 0) (sourceB530 + difference 0 2) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA530 + difference 2 0) (sourceB530 + difference 0 2) sourceC530) = raw9089 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9089; decide +kernel
    rw [ha]
    exact (canonical9089 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA530 + difference 2 1) (sourceB530 + difference 1 2) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA530 + difference 2 1) (sourceB530 + difference 1 2) sourceC530) = raw9090 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9090; decide +kernel
    rw [ha]
    exact (canonical9090 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA530 + difference 2 3) (sourceB530 + difference 3 2) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA530 + difference 2 3) (sourceB530 + difference 3 2) sourceC530) = raw9091 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9091; decide +kernel
    rw [ha]
    exact (canonical9091 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA530 + difference 2 4) (sourceB530 + difference 4 2) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA530 + difference 2 4) (sourceB530 + difference 4 2) sourceC530) = raw9092 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9092; decide +kernel
    rw [ha]
    exact (canonical9092 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA530 + difference 2 5) (sourceB530 + difference 5 2) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA530 + difference 2 5) (sourceB530 + difference 5 2) sourceC530) = raw2949 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw2949; decide +kernel
    rw [ha]
    exact (canonical2949 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA530 + difference 3 0) (sourceB530 + difference 0 3) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA530 + difference 3 0) (sourceB530 + difference 0 3) sourceC530) = raw9093 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9093; decide +kernel
    rw [ha]
    exact (canonical9093 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA530 + difference 3 1) (sourceB530 + difference 1 3) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA530 + difference 3 1) (sourceB530 + difference 1 3) sourceC530) = raw9094 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9094; decide +kernel
    rw [ha]
    exact (canonical9094 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA530 + difference 3 2) (sourceB530 + difference 2 3) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA530 + difference 3 2) (sourceB530 + difference 2 3) sourceC530) = raw9095 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9095; decide +kernel
    rw [ha]
    exact (canonical9095 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA530 + difference 3 4) (sourceB530 + difference 4 3) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA530 + difference 3 4) (sourceB530 + difference 4 3) sourceC530) = raw9096 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9096; decide +kernel
    rw [ha]
    exact (canonical9096 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA530 + difference 3 5) (sourceB530 + difference 5 3) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA530 + difference 3 5) (sourceB530 + difference 5 3) sourceC530) = raw2954 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw2954; decide +kernel
    rw [ha]
    exact (canonical2954 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA530 + difference 4 0) (sourceB530 + difference 0 4) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4586) := by
    have ha : (tripleCharges (sourceA530 + difference 4 0) (sourceB530 + difference 0 4) sourceC530) = raw9097 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9097; decide +kernel
    rw [ha]
    exact (canonical9097 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA530 + difference 4 1) (sourceB530 + difference 1 4) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5142) := by
    have ha : (tripleCharges (sourceA530 + difference 4 1) (sourceB530 + difference 1 4) sourceC530) = raw9098 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9098; decide +kernel
    rw [ha]
    exact (canonical9098 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA530 + difference 4 2) (sourceB530 + difference 2 4) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA530 + difference 4 2) (sourceB530 + difference 2 4) sourceC530) = raw9099 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9099; decide +kernel
    rw [ha]
    exact (canonical9099 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA530 + difference 4 3) (sourceB530 + difference 3 4) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA530 + difference 4 3) (sourceB530 + difference 3 4) sourceC530) = raw9100 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9100; decide +kernel
    rw [ha]
    exact (canonical9100 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA530 + difference 4 5) (sourceB530 + difference 5 4) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA530 + difference 4 5) (sourceB530 + difference 5 4) sourceC530) = raw2959 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw2959; decide +kernel
    rw [ha]
    exact (canonical2959 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA530 + difference 5 0) (sourceB530 + difference 0 5) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA530 + difference 5 0) (sourceB530 + difference 0 5) sourceC530) = raw9101 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9101; decide +kernel
    rw [ha]
    exact (canonical9101 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA530 + difference 5 1) (sourceB530 + difference 1 5) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA530 + difference 5 1) (sourceB530 + difference 1 5) sourceC530) = raw9102 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9102; decide +kernel
    rw [ha]
    exact (canonical9102 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA530 + difference 5 2) (sourceB530 + difference 2 5) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA530 + difference 5 2) (sourceB530 + difference 2 5) sourceC530) = raw9103 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9103; decide +kernel
    rw [ha]
    exact (canonical9103 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA530 + difference 5 3) (sourceB530 + difference 3 5) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA530 + difference 5 3) (sourceB530 + difference 3 5) sourceC530) = raw9104 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9104; decide +kernel
    rw [ha]
    exact (canonical9104 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA530 + difference 5 4) (sourceB530 + difference 4 5) sourceC530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA530 + difference 5 4) (sourceB530 + difference 4 5) sourceC530) = raw9105 := by
      apply Matrix.ext; unfold tripleCharges sourceA530 sourceB530 sourceC530 difference raw9105; decide +kernel
    rw [ha]
    exact (canonical9105 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA530 sourceB530 sourceC530
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm530, Integer.Sparse.eval]
  linarith only [hs]

def sourceA531 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB531 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC531 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceForm531 : Integer.Sparse Master := [(Sum.inr 1200, 1), (Sum.inr 1202, 1), (Sum.inr 1205, 1), (Sum.inr 1236, 2), (Sum.inr 1898, 1), (Sum.inr 1915, 2), (Sum.inr 2247, 1), (Sum.inr 2853, 2), (Sum.inr 2856, 2), (Sum.inr 2881, 2), (Sum.inr 2913, 1), (Sum.inr 2924, 2), (Sum.inr 3076, 1), (Sum.inr 3077, 2), (Sum.inr 3100, 2), (Sum.inr 3101, 2), (Sum.inr 3801, 1), (Sum.inr 3809, 2), (Sum.inr 3912, 1), (Sum.inr 4039, 1)]

theorem sourceEq531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm531 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA531 + difference 0 1) (sourceB531 + difference 1 0) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA531 + difference 0 1) (sourceB531 + difference 1 0) sourceC531) = raw2995 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw2995; decide +kernel
    rw [ha]
    exact (canonical2995 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA531 + difference 0 2) (sourceB531 + difference 2 0) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA531 + difference 0 2) (sourceB531 + difference 2 0) sourceC531) = raw2996 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw2996; decide +kernel
    rw [ha]
    exact (canonical2996 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA531 + difference 0 3) (sourceB531 + difference 3 0) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA531 + difference 0 3) (sourceB531 + difference 3 0) sourceC531) = raw2997 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw2997; decide +kernel
    rw [ha]
    exact (canonical2997 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA531 + difference 0 4) (sourceB531 + difference 4 0) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA531 + difference 0 4) (sourceB531 + difference 4 0) sourceC531) = raw2998 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw2998; decide +kernel
    rw [ha]
    exact (canonical2998 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA531 + difference 0 5) (sourceB531 + difference 5 0) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA531 + difference 0 5) (sourceB531 + difference 5 0) sourceC531) = raw9106 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9106; decide +kernel
    rw [ha]
    exact (canonical9106 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA531 + difference 1 0) (sourceB531 + difference 0 1) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA531 + difference 1 0) (sourceB531 + difference 0 1) sourceC531) = raw9107 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9107; decide +kernel
    rw [ha]
    exact (canonical9107 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA531 + difference 1 2) (sourceB531 + difference 2 1) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA531 + difference 1 2) (sourceB531 + difference 2 1) sourceC531) = raw9108 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9108; decide +kernel
    rw [ha]
    exact (canonical9108 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA531 + difference 1 3) (sourceB531 + difference 3 1) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA531 + difference 1 3) (sourceB531 + difference 3 1) sourceC531) = raw9109 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9109; decide +kernel
    rw [ha]
    exact (canonical9109 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA531 + difference 1 4) (sourceB531 + difference 4 1) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA531 + difference 1 4) (sourceB531 + difference 4 1) sourceC531) = raw9110 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9110; decide +kernel
    rw [ha]
    exact (canonical9110 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA531 + difference 1 5) (sourceB531 + difference 5 1) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3076) := by
    have ha : (tripleCharges (sourceA531 + difference 1 5) (sourceB531 + difference 5 1) sourceC531) = raw2974 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw2974; decide +kernel
    rw [ha]
    exact (canonical2974 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA531 + difference 2 0) (sourceB531 + difference 0 2) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA531 + difference 2 0) (sourceB531 + difference 0 2) sourceC531) = raw9111 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9111; decide +kernel
    rw [ha]
    exact (canonical9111 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA531 + difference 2 1) (sourceB531 + difference 1 2) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA531 + difference 2 1) (sourceB531 + difference 1 2) sourceC531) = raw9112 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9112; decide +kernel
    rw [ha]
    exact (canonical9112 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA531 + difference 2 3) (sourceB531 + difference 3 2) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA531 + difference 2 3) (sourceB531 + difference 3 2) sourceC531) = raw9113 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9113; decide +kernel
    rw [ha]
    exact (canonical9113 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA531 + difference 2 4) (sourceB531 + difference 4 2) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA531 + difference 2 4) (sourceB531 + difference 4 2) sourceC531) = raw9114 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9114; decide +kernel
    rw [ha]
    exact (canonical9114 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA531 + difference 2 5) (sourceB531 + difference 5 2) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA531 + difference 2 5) (sourceB531 + difference 5 2) sourceC531) = raw2979 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw2979; decide +kernel
    rw [ha]
    exact (canonical2979 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA531 + difference 3 0) (sourceB531 + difference 0 3) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA531 + difference 3 0) (sourceB531 + difference 0 3) sourceC531) = raw9115 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9115; decide +kernel
    rw [ha]
    exact (canonical9115 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA531 + difference 3 1) (sourceB531 + difference 1 3) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA531 + difference 3 1) (sourceB531 + difference 1 3) sourceC531) = raw9116 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9116; decide +kernel
    rw [ha]
    exact (canonical9116 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA531 + difference 3 2) (sourceB531 + difference 2 3) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA531 + difference 3 2) (sourceB531 + difference 2 3) sourceC531) = raw9117 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9117; decide +kernel
    rw [ha]
    exact (canonical9117 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA531 + difference 3 4) (sourceB531 + difference 4 3) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA531 + difference 3 4) (sourceB531 + difference 4 3) sourceC531) = raw9118 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9118; decide +kernel
    rw [ha]
    exact (canonical9118 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA531 + difference 3 5) (sourceB531 + difference 5 3) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA531 + difference 3 5) (sourceB531 + difference 5 3) sourceC531) = raw2984 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw2984; decide +kernel
    rw [ha]
    exact (canonical2984 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA531 + difference 4 0) (sourceB531 + difference 0 4) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1205) := by
    have ha : (tripleCharges (sourceA531 + difference 4 0) (sourceB531 + difference 0 4) sourceC531) = raw9119 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9119; decide +kernel
    rw [ha]
    exact (canonical9119 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA531 + difference 4 1) (sourceB531 + difference 1 4) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2913) := by
    have ha : (tripleCharges (sourceA531 + difference 4 1) (sourceB531 + difference 1 4) sourceC531) = raw9120 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9120; decide +kernel
    rw [ha]
    exact (canonical9120 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA531 + difference 4 2) (sourceB531 + difference 2 4) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2856) := by
    have ha : (tripleCharges (sourceA531 + difference 4 2) (sourceB531 + difference 2 4) sourceC531) = raw9121 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9121; decide +kernel
    rw [ha]
    exact (canonical9121 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA531 + difference 4 3) (sourceB531 + difference 3 4) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2856) := by
    have ha : (tripleCharges (sourceA531 + difference 4 3) (sourceB531 + difference 3 4) sourceC531) = raw9122 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9122; decide +kernel
    rw [ha]
    exact (canonical9122 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA531 + difference 4 5) (sourceB531 + difference 5 4) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA531 + difference 4 5) (sourceB531 + difference 5 4) sourceC531) = raw2989 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw2989; decide +kernel
    rw [ha]
    exact (canonical2989 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA531 + difference 5 0) (sourceB531 + difference 0 5) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA531 + difference 5 0) (sourceB531 + difference 0 5) sourceC531) = raw9123 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9123; decide +kernel
    rw [ha]
    exact (canonical9123 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA531 + difference 5 1) (sourceB531 + difference 1 5) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA531 + difference 5 1) (sourceB531 + difference 1 5) sourceC531) = raw9124 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9124; decide +kernel
    rw [ha]
    exact (canonical9124 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA531 + difference 5 2) (sourceB531 + difference 2 5) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA531 + difference 5 2) (sourceB531 + difference 2 5) sourceC531) = raw9125 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9125; decide +kernel
    rw [ha]
    exact (canonical9125 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA531 + difference 5 3) (sourceB531 + difference 3 5) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA531 + difference 5 3) (sourceB531 + difference 3 5) sourceC531) = raw9126 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9126; decide +kernel
    rw [ha]
    exact (canonical9126 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA531 + difference 5 4) (sourceB531 + difference 4 5) sourceC531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA531 + difference 5 4) (sourceB531 + difference 4 5) sourceC531) = raw9127 := by
      apply Matrix.ext; unfold tripleCharges sourceA531 sourceB531 sourceC531 difference raw9127; decide +kernel
    rw [ha]
    exact (canonical9127 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA531 sourceB531 sourceC531
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm531, Integer.Sparse.eval]
  linarith only [hs]

def sourceA532 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB532 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC532 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceForm532 : Integer.Sparse Master := [(Sum.inr 4439, 1), (Sum.inr 4440, 1), (Sum.inr 4444, 1), (Sum.inr 4459, 2), (Sum.inr 5065, 1), (Sum.inr 5067, 1), (Sum.inr 5074, 2), (Sum.inr 5078, 2), (Sum.inr 5149, 2), (Sum.inr 5152, 2), (Sum.inr 5170, 2), (Sum.inr 5251, 1), (Sum.inr 5252, 1), (Sum.inr 5260, 2), (Sum.inr 5281, 1), (Sum.inr 5282, 1), (Sum.inr 5289, 2), (Sum.inr 5405, 1), (Sum.inr 5410, 2), (Sum.inr 5439, 1), (Sum.inr 5485, 1)]

theorem sourceEq532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm532 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA532 + difference 0 1) (sourceB532 + difference 1 0) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA532 + difference 0 1) (sourceB532 + difference 1 0) sourceC532) = raw9128 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9128; decide +kernel
    rw [ha]
    exact (canonical9128 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA532 + difference 0 2) (sourceB532 + difference 2 0) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA532 + difference 0 2) (sourceB532 + difference 2 0) sourceC532) = raw9129 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9129; decide +kernel
    rw [ha]
    exact (canonical9129 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA532 + difference 0 3) (sourceB532 + difference 3 0) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA532 + difference 0 3) (sourceB532 + difference 3 0) sourceC532) = raw9130 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9130; decide +kernel
    rw [ha]
    exact (canonical9130 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA532 + difference 0 4) (sourceB532 + difference 4 0) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA532 + difference 0 4) (sourceB532 + difference 4 0) sourceC532) = raw9131 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9131; decide +kernel
    rw [ha]
    exact (canonical9131 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA532 + difference 0 5) (sourceB532 + difference 5 0) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA532 + difference 0 5) (sourceB532 + difference 5 0) sourceC532) = raw9132 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9132; decide +kernel
    rw [ha]
    exact (canonical9132 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA532 + difference 1 0) (sourceB532 + difference 0 1) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA532 + difference 1 0) (sourceB532 + difference 0 1) sourceC532) = raw9133 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9133; decide +kernel
    rw [ha]
    exact (canonical9133 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA532 + difference 1 2) (sourceB532 + difference 2 1) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA532 + difference 1 2) (sourceB532 + difference 2 1) sourceC532) = raw9134 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9134; decide +kernel
    rw [ha]
    exact (canonical9134 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA532 + difference 1 3) (sourceB532 + difference 3 1) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA532 + difference 1 3) (sourceB532 + difference 3 1) sourceC532) = raw9135 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9135; decide +kernel
    rw [ha]
    exact (canonical9135 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA532 + difference 1 4) (sourceB532 + difference 4 1) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA532 + difference 1 4) (sourceB532 + difference 4 1) sourceC532) = raw9136 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9136; decide +kernel
    rw [ha]
    exact (canonical9136 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA532 + difference 1 5) (sourceB532 + difference 5 1) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA532 + difference 1 5) (sourceB532 + difference 5 1) sourceC532) = raw9137 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9137; decide +kernel
    rw [ha]
    exact (canonical9137 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA532 + difference 2 0) (sourceB532 + difference 0 2) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA532 + difference 2 0) (sourceB532 + difference 0 2) sourceC532) = raw9138 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9138; decide +kernel
    rw [ha]
    exact (canonical9138 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA532 + difference 2 1) (sourceB532 + difference 1 2) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA532 + difference 2 1) (sourceB532 + difference 1 2) sourceC532) = raw9139 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9139; decide +kernel
    rw [ha]
    exact (canonical9139 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA532 + difference 2 3) (sourceB532 + difference 3 2) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA532 + difference 2 3) (sourceB532 + difference 3 2) sourceC532) = raw9140 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9140; decide +kernel
    rw [ha]
    exact (canonical9140 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA532 + difference 2 4) (sourceB532 + difference 4 2) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA532 + difference 2 4) (sourceB532 + difference 4 2) sourceC532) = raw9141 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9141; decide +kernel
    rw [ha]
    exact (canonical9141 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA532 + difference 2 5) (sourceB532 + difference 5 2) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA532 + difference 2 5) (sourceB532 + difference 5 2) sourceC532) = raw9142 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9142; decide +kernel
    rw [ha]
    exact (canonical9142 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA532 + difference 3 0) (sourceB532 + difference 0 3) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA532 + difference 3 0) (sourceB532 + difference 0 3) sourceC532) = raw9143 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9143; decide +kernel
    rw [ha]
    exact (canonical9143 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA532 + difference 3 1) (sourceB532 + difference 1 3) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA532 + difference 3 1) (sourceB532 + difference 1 3) sourceC532) = raw9144 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9144; decide +kernel
    rw [ha]
    exact (canonical9144 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA532 + difference 3 2) (sourceB532 + difference 2 3) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA532 + difference 3 2) (sourceB532 + difference 2 3) sourceC532) = raw9145 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9145; decide +kernel
    rw [ha]
    exact (canonical9145 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA532 + difference 3 4) (sourceB532 + difference 4 3) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA532 + difference 3 4) (sourceB532 + difference 4 3) sourceC532) = raw9146 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9146; decide +kernel
    rw [ha]
    exact (canonical9146 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA532 + difference 3 5) (sourceB532 + difference 5 3) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA532 + difference 3 5) (sourceB532 + difference 5 3) sourceC532) = raw9147 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9147; decide +kernel
    rw [ha]
    exact (canonical9147 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA532 + difference 4 0) (sourceB532 + difference 0 4) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA532 + difference 4 0) (sourceB532 + difference 0 4) sourceC532) = raw9148 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9148; decide +kernel
    rw [ha]
    exact (canonical9148 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA532 + difference 4 1) (sourceB532 + difference 1 4) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA532 + difference 4 1) (sourceB532 + difference 1 4) sourceC532) = raw9149 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9149; decide +kernel
    rw [ha]
    exact (canonical9149 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA532 + difference 4 2) (sourceB532 + difference 2 4) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA532 + difference 4 2) (sourceB532 + difference 2 4) sourceC532) = raw9150 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9150; decide +kernel
    rw [ha]
    exact (canonical9150 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA532 + difference 4 3) (sourceB532 + difference 3 4) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA532 + difference 4 3) (sourceB532 + difference 3 4) sourceC532) = raw9151 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9151; decide +kernel
    rw [ha]
    exact (canonical9151 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA532 + difference 4 5) (sourceB532 + difference 5 4) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA532 + difference 4 5) (sourceB532 + difference 5 4) sourceC532) = raw9152 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9152; decide +kernel
    rw [ha]
    exact (canonical9152 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA532 + difference 5 0) (sourceB532 + difference 0 5) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA532 + difference 5 0) (sourceB532 + difference 0 5) sourceC532) = raw9153 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9153; decide +kernel
    rw [ha]
    exact (canonical9153 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA532 + difference 5 1) (sourceB532 + difference 1 5) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5065) := by
    have ha : (tripleCharges (sourceA532 + difference 5 1) (sourceB532 + difference 1 5) sourceC532) = raw9154 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9154; decide +kernel
    rw [ha]
    exact (canonical9154 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA532 + difference 5 2) (sourceB532 + difference 2 5) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA532 + difference 5 2) (sourceB532 + difference 2 5) sourceC532) = raw9155 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9155; decide +kernel
    rw [ha]
    exact (canonical9155 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA532 + difference 5 3) (sourceB532 + difference 3 5) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA532 + difference 5 3) (sourceB532 + difference 3 5) sourceC532) = raw9156 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9156; decide +kernel
    rw [ha]
    exact (canonical9156 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA532 + difference 5 4) (sourceB532 + difference 4 5) sourceC532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA532 + difference 5 4) (sourceB532 + difference 4 5) sourceC532) = raw9157 := by
      apply Matrix.ext; unfold tripleCharges sourceA532 sourceB532 sourceC532 difference raw9157; decide +kernel
    rw [ha]
    exact (canonical9157 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA532 sourceB532 sourceC532
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm532, Integer.Sparse.eval]
  linarith only [hs]

def sourceA533 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB533 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC533 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceForm533 : Integer.Sparse Master := [(Sum.inr 1021, 1), (Sum.inr 1022, 1), (Sum.inr 1026, 1), (Sum.inr 1042, 2), (Sum.inr 2470, 1), (Sum.inr 2473, 1), (Sum.inr 2481, 2), (Sum.inr 2570, 2), (Sum.inr 2572, 2), (Sum.inr 2576, 2), (Sum.inr 2596, 2), (Sum.inr 2710, 1), (Sum.inr 2712, 1), (Sum.inr 2724, 2), (Sum.inr 2750, 1), (Sum.inr 2751, 1), (Sum.inr 2763, 2), (Sum.inr 3977, 1), (Sum.inr 3996, 2), (Sum.inr 3998, 1), (Sum.inr 4012, 1)]

theorem sourceEq533 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm533 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA533 + difference 0 1) (sourceB533 + difference 1 0) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA533 + difference 0 1) (sourceB533 + difference 1 0) sourceC533) = raw9158 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9158; decide +kernel
    rw [ha]
    exact (canonical9158 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA533 + difference 0 2) (sourceB533 + difference 2 0) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3996) := by
    have ha : (tripleCharges (sourceA533 + difference 0 2) (sourceB533 + difference 2 0) sourceC533) = raw9159 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9159; decide +kernel
    rw [ha]
    exact (canonical9159 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA533 + difference 0 3) (sourceB533 + difference 3 0) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3996) := by
    have ha : (tripleCharges (sourceA533 + difference 0 3) (sourceB533 + difference 3 0) sourceC533) = raw9160 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9160; decide +kernel
    rw [ha]
    exact (canonical9160 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA533 + difference 0 4) (sourceB533 + difference 4 0) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA533 + difference 0 4) (sourceB533 + difference 4 0) sourceC533) = raw9161 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9161; decide +kernel
    rw [ha]
    exact (canonical9161 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA533 + difference 0 5) (sourceB533 + difference 5 0) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA533 + difference 0 5) (sourceB533 + difference 5 0) sourceC533) = raw9162 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9162; decide +kernel
    rw [ha]
    exact (canonical9162 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA533 + difference 1 0) (sourceB533 + difference 0 1) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA533 + difference 1 0) (sourceB533 + difference 0 1) sourceC533) = raw9163 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9163; decide +kernel
    rw [ha]
    exact (canonical9163 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA533 + difference 1 2) (sourceB533 + difference 2 1) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2570) := by
    have ha : (tripleCharges (sourceA533 + difference 1 2) (sourceB533 + difference 2 1) sourceC533) = raw9164 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9164; decide +kernel
    rw [ha]
    exact (canonical9164 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA533 + difference 1 3) (sourceB533 + difference 3 1) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2570) := by
    have ha : (tripleCharges (sourceA533 + difference 1 3) (sourceB533 + difference 3 1) sourceC533) = raw9165 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9165; decide +kernel
    rw [ha]
    exact (canonical9165 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA533 + difference 1 4) (sourceB533 + difference 4 1) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA533 + difference 1 4) (sourceB533 + difference 4 1) sourceC533) = raw9166 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9166; decide +kernel
    rw [ha]
    exact (canonical9166 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA533 + difference 1 5) (sourceB533 + difference 5 1) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA533 + difference 1 5) (sourceB533 + difference 5 1) sourceC533) = raw9167 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9167; decide +kernel
    rw [ha]
    exact (canonical9167 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA533 + difference 2 0) (sourceB533 + difference 0 2) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA533 + difference 2 0) (sourceB533 + difference 0 2) sourceC533) = raw9168 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9168; decide +kernel
    rw [ha]
    exact (canonical9168 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA533 + difference 2 1) (sourceB533 + difference 1 2) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA533 + difference 2 1) (sourceB533 + difference 1 2) sourceC533) = raw9169 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9169; decide +kernel
    rw [ha]
    exact (canonical9169 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA533 + difference 2 3) (sourceB533 + difference 3 2) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2596) := by
    have ha : (tripleCharges (sourceA533 + difference 2 3) (sourceB533 + difference 3 2) sourceC533) = raw9170 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9170; decide +kernel
    rw [ha]
    exact (canonical9170 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA533 + difference 2 4) (sourceB533 + difference 4 2) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA533 + difference 2 4) (sourceB533 + difference 4 2) sourceC533) = raw9171 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9171; decide +kernel
    rw [ha]
    exact (canonical9171 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA533 + difference 2 5) (sourceB533 + difference 5 2) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA533 + difference 2 5) (sourceB533 + difference 5 2) sourceC533) = raw9172 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9172; decide +kernel
    rw [ha]
    exact (canonical9172 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA533 + difference 3 0) (sourceB533 + difference 0 3) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA533 + difference 3 0) (sourceB533 + difference 0 3) sourceC533) = raw9173 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9173; decide +kernel
    rw [ha]
    exact (canonical9173 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA533 + difference 3 1) (sourceB533 + difference 1 3) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA533 + difference 3 1) (sourceB533 + difference 1 3) sourceC533) = raw9174 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9174; decide +kernel
    rw [ha]
    exact (canonical9174 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA533 + difference 3 2) (sourceB533 + difference 2 3) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2596) := by
    have ha : (tripleCharges (sourceA533 + difference 3 2) (sourceB533 + difference 2 3) sourceC533) = raw9175 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9175; decide +kernel
    rw [ha]
    exact (canonical9175 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA533 + difference 3 4) (sourceB533 + difference 4 3) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA533 + difference 3 4) (sourceB533 + difference 4 3) sourceC533) = raw9176 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9176; decide +kernel
    rw [ha]
    exact (canonical9176 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA533 + difference 3 5) (sourceB533 + difference 5 3) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA533 + difference 3 5) (sourceB533 + difference 5 3) sourceC533) = raw9177 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9177; decide +kernel
    rw [ha]
    exact (canonical9177 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA533 + difference 4 0) (sourceB533 + difference 0 4) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA533 + difference 4 0) (sourceB533 + difference 0 4) sourceC533) = raw9178 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9178; decide +kernel
    rw [ha]
    exact (canonical9178 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA533 + difference 4 1) (sourceB533 + difference 1 4) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA533 + difference 4 1) (sourceB533 + difference 1 4) sourceC533) = raw9179 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9179; decide +kernel
    rw [ha]
    exact (canonical9179 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA533 + difference 4 2) (sourceB533 + difference 2 4) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA533 + difference 4 2) (sourceB533 + difference 2 4) sourceC533) = raw9180 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9180; decide +kernel
    rw [ha]
    exact (canonical9180 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA533 + difference 4 3) (sourceB533 + difference 3 4) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA533 + difference 4 3) (sourceB533 + difference 3 4) sourceC533) = raw9181 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9181; decide +kernel
    rw [ha]
    exact (canonical9181 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA533 + difference 4 5) (sourceB533 + difference 5 4) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA533 + difference 4 5) (sourceB533 + difference 5 4) sourceC533) = raw9182 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9182; decide +kernel
    rw [ha]
    exact (canonical9182 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA533 + difference 5 0) (sourceB533 + difference 0 5) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA533 + difference 5 0) (sourceB533 + difference 0 5) sourceC533) = raw9183 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9183; decide +kernel
    rw [ha]
    exact (canonical9183 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA533 + difference 5 1) (sourceB533 + difference 1 5) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA533 + difference 5 1) (sourceB533 + difference 1 5) sourceC533) = raw9184 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9184; decide +kernel
    rw [ha]
    exact (canonical9184 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA533 + difference 5 2) (sourceB533 + difference 2 5) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2572) := by
    have ha : (tripleCharges (sourceA533 + difference 5 2) (sourceB533 + difference 2 5) sourceC533) = raw9185 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9185; decide +kernel
    rw [ha]
    exact (canonical9185 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA533 + difference 5 3) (sourceB533 + difference 3 5) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2572) := by
    have ha : (tripleCharges (sourceA533 + difference 5 3) (sourceB533 + difference 3 5) sourceC533) = raw9186 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9186; decide +kernel
    rw [ha]
    exact (canonical9186 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA533 + difference 5 4) (sourceB533 + difference 4 5) sourceC533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA533 + difference 5 4) (sourceB533 + difference 4 5) sourceC533) = raw9187 := by
      apply Matrix.ext; unfold tripleCharges sourceA533 sourceB533 sourceC533 difference raw9187; decide +kernel
    rw [ha]
    exact (canonical9187 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA533 sourceB533 sourceC533
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm533, Integer.Sparse.eval]
  linarith only [hs]

def sourceA534 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB534 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC534 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceForm534 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 1714, 2), (Sum.inr 1723, 1), (Sum.inr 1736, 1), (Sum.inr 3463, 2), (Sum.inr 3466, 1), (Sum.inr 3476, 1), (Sum.inr 3481, 2), (Sum.inr 3539, 1), (Sum.inr 3540, 2), (Sum.inr 3543, 1), (Sum.inr 3571, 1), (Sum.inr 3572, 2), (Sum.inr 3580, 1), (Sum.inr 3605, 2), (Sum.inr 3606, 2), (Sum.inr 3612, 2), (Sum.inr 3805, 1), (Sum.inr 3816, 2), (Sum.inr 3858, 1), (Sum.inr 3984, 1)]

theorem sourceEq534 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm534 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA534 + difference 0 1) (sourceB534 + difference 1 0) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA534 + difference 0 1) (sourceB534 + difference 1 0) sourceC534) = raw9188 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9188; decide +kernel
    rw [ha]
    exact (canonical9188 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA534 + difference 0 2) (sourceB534 + difference 2 0) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA534 + difference 0 2) (sourceB534 + difference 2 0) sourceC534) = raw9189 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9189; decide +kernel
    rw [ha]
    exact (canonical9189 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA534 + difference 0 3) (sourceB534 + difference 3 0) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA534 + difference 0 3) (sourceB534 + difference 3 0) sourceC534) = raw9190 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9190; decide +kernel
    rw [ha]
    exact (canonical9190 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA534 + difference 0 4) (sourceB534 + difference 4 0) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA534 + difference 0 4) (sourceB534 + difference 4 0) sourceC534) = raw9191 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9191; decide +kernel
    rw [ha]
    exact (canonical9191 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA534 + difference 0 5) (sourceB534 + difference 5 0) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA534 + difference 0 5) (sourceB534 + difference 5 0) sourceC534) = raw9192 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9192; decide +kernel
    rw [ha]
    exact (canonical9192 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA534 + difference 1 0) (sourceB534 + difference 0 1) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA534 + difference 1 0) (sourceB534 + difference 0 1) sourceC534) = raw9193 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9193; decide +kernel
    rw [ha]
    exact (canonical9193 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA534 + difference 1 2) (sourceB534 + difference 2 1) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA534 + difference 1 2) (sourceB534 + difference 2 1) sourceC534) = raw9194 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9194; decide +kernel
    rw [ha]
    exact (canonical9194 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA534 + difference 1 3) (sourceB534 + difference 3 1) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA534 + difference 1 3) (sourceB534 + difference 3 1) sourceC534) = raw9195 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9195; decide +kernel
    rw [ha]
    exact (canonical9195 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA534 + difference 1 4) (sourceB534 + difference 4 1) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA534 + difference 1 4) (sourceB534 + difference 4 1) sourceC534) = raw9196 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9196; decide +kernel
    rw [ha]
    exact (canonical9196 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA534 + difference 1 5) (sourceB534 + difference 5 1) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA534 + difference 1 5) (sourceB534 + difference 5 1) sourceC534) = raw9197 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9197; decide +kernel
    rw [ha]
    exact (canonical9197 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA534 + difference 2 0) (sourceB534 + difference 0 2) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA534 + difference 2 0) (sourceB534 + difference 0 2) sourceC534) = raw9198 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9198; decide +kernel
    rw [ha]
    exact (canonical9198 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA534 + difference 2 1) (sourceB534 + difference 1 2) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA534 + difference 2 1) (sourceB534 + difference 1 2) sourceC534) = raw9199 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9199; decide +kernel
    rw [ha]
    exact (canonical9199 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA534 + difference 2 3) (sourceB534 + difference 3 2) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA534 + difference 2 3) (sourceB534 + difference 3 2) sourceC534) = raw9200 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9200; decide +kernel
    rw [ha]
    exact (canonical9200 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA534 + difference 2 4) (sourceB534 + difference 4 2) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA534 + difference 2 4) (sourceB534 + difference 4 2) sourceC534) = raw9201 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9201; decide +kernel
    rw [ha]
    exact (canonical9201 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA534 + difference 2 5) (sourceB534 + difference 5 2) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA534 + difference 2 5) (sourceB534 + difference 5 2) sourceC534) = raw9202 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9202; decide +kernel
    rw [ha]
    exact (canonical9202 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA534 + difference 3 0) (sourceB534 + difference 0 3) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA534 + difference 3 0) (sourceB534 + difference 0 3) sourceC534) = raw9203 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9203; decide +kernel
    rw [ha]
    exact (canonical9203 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA534 + difference 3 1) (sourceB534 + difference 1 3) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA534 + difference 3 1) (sourceB534 + difference 1 3) sourceC534) = raw9204 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9204; decide +kernel
    rw [ha]
    exact (canonical9204 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA534 + difference 3 2) (sourceB534 + difference 2 3) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA534 + difference 3 2) (sourceB534 + difference 2 3) sourceC534) = raw9205 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9205; decide +kernel
    rw [ha]
    exact (canonical9205 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA534 + difference 3 4) (sourceB534 + difference 4 3) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA534 + difference 3 4) (sourceB534 + difference 4 3) sourceC534) = raw9206 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9206; decide +kernel
    rw [ha]
    exact (canonical9206 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA534 + difference 3 5) (sourceB534 + difference 5 3) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA534 + difference 3 5) (sourceB534 + difference 5 3) sourceC534) = raw9207 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9207; decide +kernel
    rw [ha]
    exact (canonical9207 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA534 + difference 4 0) (sourceB534 + difference 0 4) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA534 + difference 4 0) (sourceB534 + difference 0 4) sourceC534) = raw9208 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9208; decide +kernel
    rw [ha]
    exact (canonical9208 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA534 + difference 4 1) (sourceB534 + difference 1 4) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA534 + difference 4 1) (sourceB534 + difference 1 4) sourceC534) = raw9209 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9209; decide +kernel
    rw [ha]
    exact (canonical9209 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA534 + difference 4 2) (sourceB534 + difference 2 4) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA534 + difference 4 2) (sourceB534 + difference 2 4) sourceC534) = raw9210 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9210; decide +kernel
    rw [ha]
    exact (canonical9210 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA534 + difference 4 3) (sourceB534 + difference 3 4) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA534 + difference 4 3) (sourceB534 + difference 3 4) sourceC534) = raw9211 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9211; decide +kernel
    rw [ha]
    exact (canonical9211 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA534 + difference 4 5) (sourceB534 + difference 5 4) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA534 + difference 4 5) (sourceB534 + difference 5 4) sourceC534) = raw9212 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9212; decide +kernel
    rw [ha]
    exact (canonical9212 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA534 + difference 5 0) (sourceB534 + difference 0 5) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA534 + difference 5 0) (sourceB534 + difference 0 5) sourceC534) = raw9213 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9213; decide +kernel
    rw [ha]
    exact (canonical9213 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA534 + difference 5 1) (sourceB534 + difference 1 5) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA534 + difference 5 1) (sourceB534 + difference 1 5) sourceC534) = raw9214 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9214; decide +kernel
    rw [ha]
    exact (canonical9214 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA534 + difference 5 2) (sourceB534 + difference 2 5) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA534 + difference 5 2) (sourceB534 + difference 2 5) sourceC534) = raw9215 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9215; decide +kernel
    rw [ha]
    exact (canonical9215 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA534 + difference 5 3) (sourceB534 + difference 3 5) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA534 + difference 5 3) (sourceB534 + difference 3 5) sourceC534) = raw9216 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9216; decide +kernel
    rw [ha]
    exact (canonical9216 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA534 + difference 5 4) (sourceB534 + difference 4 5) sourceC534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA534 + difference 5 4) (sourceB534 + difference 4 5) sourceC534) = raw9217 := by
      apply Matrix.ext; unfold tripleCharges sourceA534 sourceB534 sourceC534 difference raw9217; decide +kernel
    rw [ha]
    exact (canonical9217 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA534 sourceB534 sourceC534
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm534, Integer.Sparse.eval]
  linarith only [hs]

def sourceA535 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB535 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC535 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceForm535 : Integer.Sparse Master := [(Sum.inr 3077, 1), (Sum.inr 3800, 1), (Sum.inr 3808, 2), (Sum.inr 3902, 1), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

theorem sourceEq535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm535 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA535 + difference 0 0) (sourceB535 + difference 0 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA535 + difference 0 0) (sourceB535 + difference 0 0) sourceC535) = raw9218 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9218; decide +kernel
    rw [ha]
    exact (canonical9218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA535 + difference 0 1) (sourceB535 + difference 1 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA535 + difference 0 1) (sourceB535 + difference 1 0) sourceC535) = raw9219 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9219; decide +kernel
    rw [ha]
    exact (canonical9219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA535 + difference 0 2) (sourceB535 + difference 2 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA535 + difference 0 2) (sourceB535 + difference 2 0) sourceC535) = raw9220 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9220; decide +kernel
    rw [ha]
    exact (canonical9220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA535 + difference 0 3) (sourceB535 + difference 3 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA535 + difference 0 3) (sourceB535 + difference 3 0) sourceC535) = raw9221 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9221; decide +kernel
    rw [ha]
    exact (canonical9221 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA535 + difference 0 4) (sourceB535 + difference 4 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA535 + difference 0 4) (sourceB535 + difference 4 0) sourceC535) = raw9222 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9222; decide +kernel
    rw [ha]
    exact (canonical9222 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA535 + difference 0 5) (sourceB535 + difference 5 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA535 + difference 0 5) (sourceB535 + difference 5 0) sourceC535) = raw9223 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9223; decide +kernel
    rw [ha]
    exact (canonical9223 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA535 + sourceB535) sourceC535) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA535 + sourceB535) sourceC535) = raw9224 := by
      apply Matrix.ext; unfold doubleCharges sourceA535 sourceB535 sourceC535 raw9224; decide +kernel
    rw [ha]
    exact (canonical9224 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA535 sourceB535 sourceC535
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm535, Integer.Sparse.eval]
  linarith only [hs]

def sourceA536 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB536 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC536 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceForm536 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 1388, 1), (Sum.inr 1391, 1), (Sum.inr 1406, 2), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

theorem sourceEq536 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm536 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA536 + difference 0 0) (sourceB536 + difference 0 0) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA536 + difference 0 0) (sourceB536 + difference 0 0) sourceC536) = raw9218 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9218; decide +kernel
    rw [ha]
    exact (canonical9218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA536 + difference 1 0) (sourceB536 + difference 0 1) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA536 + difference 1 0) (sourceB536 + difference 0 1) sourceC536) = raw9225 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9225; decide +kernel
    rw [ha]
    exact (canonical9225 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA536 + difference 2 0) (sourceB536 + difference 0 2) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA536 + difference 2 0) (sourceB536 + difference 0 2) sourceC536) = raw9226 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9226; decide +kernel
    rw [ha]
    exact (canonical9226 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA536 + difference 3 0) (sourceB536 + difference 0 3) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA536 + difference 3 0) (sourceB536 + difference 0 3) sourceC536) = raw9227 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9227; decide +kernel
    rw [ha]
    exact (canonical9227 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA536 + difference 4 0) (sourceB536 + difference 0 4) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA536 + difference 4 0) (sourceB536 + difference 0 4) sourceC536) = raw9228 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9228; decide +kernel
    rw [ha]
    exact (canonical9228 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA536 + difference 5 0) (sourceB536 + difference 0 5) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA536 + difference 5 0) (sourceB536 + difference 0 5) sourceC536) = raw9229 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9229; decide +kernel
    rw [ha]
    exact (canonical9229 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA536 + sourceB536) sourceC536) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA536 + sourceB536) sourceC536) = raw9224 := by
      apply Matrix.ext; unfold doubleCharges sourceA536 sourceB536 sourceC536 raw9224; decide +kernel
    rw [ha]
    exact (canonical9224 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA536 sourceB536 sourceC536
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm536, Integer.Sparse.eval]
  linarith only [hs]

def sourceA537 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB537 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC537 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceForm537 : Integer.Sparse Master := [(Sum.inr 2470, 1), (Sum.inr 2981, 1), (Sum.inr 2984, 2), (Sum.inr 3077, 1), (Sum.inr 3800, 1), (Sum.inr 4091, -1)]

theorem sourceEq537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm537 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA537 + difference 0 1) (sourceB537 + difference 1 0) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA537 + difference 0 1) (sourceB537 + difference 1 0) sourceC537) = raw9219 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9219; decide +kernel
    rw [ha]
    exact (canonical9219 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA537 + difference 1 1) (sourceB537 + difference 1 1) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA537 + difference 1 1) (sourceB537 + difference 1 1) sourceC537) = raw9218 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9218; decide +kernel
    rw [ha]
    exact (canonical9218 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA537 + difference 2 1) (sourceB537 + difference 1 2) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA537 + difference 2 1) (sourceB537 + difference 1 2) sourceC537) = raw9230 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9230; decide +kernel
    rw [ha]
    exact (canonical9230 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA537 + difference 3 1) (sourceB537 + difference 1 3) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA537 + difference 3 1) (sourceB537 + difference 1 3) sourceC537) = raw9231 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9231; decide +kernel
    rw [ha]
    exact (canonical9231 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA537 + difference 4 1) (sourceB537 + difference 1 4) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA537 + difference 4 1) (sourceB537 + difference 1 4) sourceC537) = raw9232 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9232; decide +kernel
    rw [ha]
    exact (canonical9232 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA537 + difference 5 1) (sourceB537 + difference 1 5) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA537 + difference 5 1) (sourceB537 + difference 1 5) sourceC537) = raw9233 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9233; decide +kernel
    rw [ha]
    exact (canonical9233 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA537 + sourceB537) sourceC537) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA537 + sourceB537) sourceC537) = raw9224 := by
      apply Matrix.ext; unfold doubleCharges sourceA537 sourceB537 sourceC537 raw9224; decide +kernel
    rw [ha]
    exact (canonical9224 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA537 sourceB537 sourceC537
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm537, Integer.Sparse.eval]
  linarith only [hs]

def sourceA538 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB538 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC538 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm538 : Integer.Sparse Master := [(Sum.inr 4885, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 1), (Sum.inr 4891, 2), (Sum.inr 5097, 1), (Sum.inr 5099, 1), (Sum.inr 5103, 2), (Sum.inr 5241, 1), (Sum.inr 5248, 1), (Sum.inr 5250, 1), (Sum.inr 5251, 1), (Sum.inr 5254, 2), (Sum.inr 5270, 1), (Sum.inr 5274, 2), (Sum.inr 5277, 1), (Sum.inr 5282, 1), (Sum.inr 5284, 2), (Sum.inr 5287, 2), (Sum.inr 5293, 2), (Sum.inr 5294, 2), (Sum.inr 5302, 2)]

theorem sourceEq538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm538 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA538 + difference 0 1) (sourceB538 + difference 1 0) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA538 + difference 0 1) (sourceB538 + difference 1 0) sourceC538) = raw7224 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw7224; decide +kernel
    rw [ha]
    exact (canonical7224 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA538 + difference 0 2) (sourceB538 + difference 2 0) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA538 + difference 0 2) (sourceB538 + difference 2 0) sourceC538) = raw7921 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw7921; decide +kernel
    rw [ha]
    exact (canonical7921 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA538 + difference 0 3) (sourceB538 + difference 3 0) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA538 + difference 0 3) (sourceB538 + difference 3 0) sourceC538) = raw9234 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw9234; decide +kernel
    rw [ha]
    exact (canonical9234 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA538 + difference 0 4) (sourceB538 + difference 4 0) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA538 + difference 0 4) (sourceB538 + difference 4 0) sourceC538) = raw9040 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw9040; decide +kernel
    rw [ha]
    exact (canonical9040 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA538 + difference 0 5) (sourceB538 + difference 5 0) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA538 + difference 0 5) (sourceB538 + difference 5 0) sourceC538) = raw9235 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw9235; decide +kernel
    rw [ha]
    exact (canonical9235 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA538 + difference 1 0) (sourceB538 + difference 0 1) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA538 + difference 1 0) (sourceB538 + difference 0 1) sourceC538) = raw9236 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw9236; decide +kernel
    rw [ha]
    exact (canonical9236 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA538 + difference 1 2) (sourceB538 + difference 2 1) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA538 + difference 1 2) (sourceB538 + difference 2 1) sourceC538) = raw5659 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw5659; decide +kernel
    rw [ha]
    exact (canonical5659 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA538 + difference 1 3) (sourceB538 + difference 3 1) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA538 + difference 1 3) (sourceB538 + difference 3 1) sourceC538) = raw5660 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw5660; decide +kernel
    rw [ha]
    exact (canonical5660 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA538 + difference 1 4) (sourceB538 + difference 4 1) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5277) := by
    have ha : (tripleCharges (sourceA538 + difference 1 4) (sourceB538 + difference 4 1) sourceC538) = raw5661 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw5661; decide +kernel
    rw [ha]
    exact (canonical5661 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA538 + difference 1 5) (sourceB538 + difference 5 1) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5097) := by
    have ha : (tripleCharges (sourceA538 + difference 1 5) (sourceB538 + difference 5 1) sourceC538) = raw5662 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw5662; decide +kernel
    rw [ha]
    exact (canonical5662 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA538 + difference 2 0) (sourceB538 + difference 0 2) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA538 + difference 2 0) (sourceB538 + difference 0 2) sourceC538) = raw5669 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw5669; decide +kernel
    rw [ha]
    exact (canonical5669 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA538 + difference 2 1) (sourceB538 + difference 1 2) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA538 + difference 2 1) (sourceB538 + difference 1 2) sourceC538) = raw7231 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw7231; decide +kernel
    rw [ha]
    exact (canonical7231 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA538 + difference 2 3) (sourceB538 + difference 3 2) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA538 + difference 2 3) (sourceB538 + difference 3 2) sourceC538) = raw9237 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw9237; decide +kernel
    rw [ha]
    exact (canonical9237 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA538 + difference 2 4) (sourceB538 + difference 4 2) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA538 + difference 2 4) (sourceB538 + difference 4 2) sourceC538) = raw9046 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw9046; decide +kernel
    rw [ha]
    exact (canonical9046 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA538 + difference 2 5) (sourceB538 + difference 5 2) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA538 + difference 2 5) (sourceB538 + difference 5 2) sourceC538) = raw9238 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw9238; decide +kernel
    rw [ha]
    exact (canonical9238 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA538 + difference 3 0) (sourceB538 + difference 0 3) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA538 + difference 3 0) (sourceB538 + difference 0 3) sourceC538) = raw5674 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw5674; decide +kernel
    rw [ha]
    exact (canonical5674 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA538 + difference 3 1) (sourceB538 + difference 1 3) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA538 + difference 3 1) (sourceB538 + difference 1 3) sourceC538) = raw6714 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw6714; decide +kernel
    rw [ha]
    exact (canonical6714 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA538 + difference 3 2) (sourceB538 + difference 2 3) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA538 + difference 3 2) (sourceB538 + difference 2 3) sourceC538) = raw6709 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw6709; decide +kernel
    rw [ha]
    exact (canonical6709 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA538 + difference 3 4) (sourceB538 + difference 4 3) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA538 + difference 3 4) (sourceB538 + difference 4 3) sourceC538) = raw8562 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw8562; decide +kernel
    rw [ha]
    exact (canonical8562 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA538 + difference 3 5) (sourceB538 + difference 5 3) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA538 + difference 3 5) (sourceB538 + difference 5 3) sourceC538) = raw8790 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw8790; decide +kernel
    rw [ha]
    exact (canonical8790 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA538 + difference 4 0) (sourceB538 + difference 0 4) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA538 + difference 4 0) (sourceB538 + difference 0 4) sourceC538) = raw5679 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw5679; decide +kernel
    rw [ha]
    exact (canonical5679 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA538 + difference 4 1) (sourceB538 + difference 1 4) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA538 + difference 4 1) (sourceB538 + difference 1 4) sourceC538) = raw6379 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw6379; decide +kernel
    rw [ha]
    exact (canonical6379 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA538 + difference 4 2) (sourceB538 + difference 2 4) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA538 + difference 4 2) (sourceB538 + difference 2 4) sourceC538) = raw6375 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw6375; decide +kernel
    rw [ha]
    exact (canonical6375 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA538 + difference 4 3) (sourceB538 + difference 3 4) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA538 + difference 4 3) (sourceB538 + difference 3 4) sourceC538) = raw7527 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw7527; decide +kernel
    rw [ha]
    exact (canonical7527 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA538 + difference 4 5) (sourceB538 + difference 5 4) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA538 + difference 4 5) (sourceB538 + difference 5 4) sourceC538) = raw7528 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw7528; decide +kernel
    rw [ha]
    exact (canonical7528 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA538 + difference 5 0) (sourceB538 + difference 0 5) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA538 + difference 5 0) (sourceB538 + difference 0 5) sourceC538) = raw5684 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw5684; decide +kernel
    rw [ha]
    exact (canonical5684 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA538 + difference 5 1) (sourceB538 + difference 1 5) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA538 + difference 5 1) (sourceB538 + difference 1 5) sourceC538) = raw6712 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw6712; decide +kernel
    rw [ha]
    exact (canonical6712 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA538 + difference 5 2) (sourceB538 + difference 2 5) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA538 + difference 5 2) (sourceB538 + difference 2 5) sourceC538) = raw6707 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw6707; decide +kernel
    rw [ha]
    exact (canonical6707 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA538 + difference 5 3) (sourceB538 + difference 3 5) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA538 + difference 5 3) (sourceB538 + difference 3 5) sourceC538) = raw7225 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw7225; decide +kernel
    rw [ha]
    exact (canonical7225 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA538 + difference 5 4) (sourceB538 + difference 4 5) sourceC538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA538 + difference 5 4) (sourceB538 + difference 4 5) sourceC538) = raw7226 := by
      apply Matrix.ext; unfold tripleCharges sourceA538 sourceB538 sourceC538 difference raw7226; decide +kernel
    rw [ha]
    exact (canonical7226 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA538 sourceB538 sourceC538
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm538, Integer.Sparse.eval]
  linarith only [hs]

def sourceA539 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB539 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC539 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm539 : Integer.Sparse Master := [(Sum.inr 2233, 1), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 2253, 2), (Sum.inr 2709, 1), (Sum.inr 2710, 1), (Sum.inr 2714, 2), (Sum.inr 2745, 1), (Sum.inr 2746, 1), (Sum.inr 2751, 1), (Sum.inr 2753, 2), (Sum.inr 2754, 1), (Sum.inr 2758, 2), (Sum.inr 2759, 2), (Sum.inr 2767, 2), (Sum.inr 2768, 2), (Sum.inr 2776, 2), (Sum.inr 3003, 1), (Sum.inr 3081, 1), (Sum.inr 3106, 1), (Sum.inr 3112, 2)]

theorem sourceEq539 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm539 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA539 + difference 0 1) (sourceB539 + difference 1 0) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3081) := by
    have ha : (tripleCharges (sourceA539 + difference 0 1) (sourceB539 + difference 1 0) sourceC539) = raw7242 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw7242; decide +kernel
    rw [ha]
    exact (canonical7242 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA539 + difference 0 2) (sourceB539 + difference 2 0) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA539 + difference 0 2) (sourceB539 + difference 2 0) sourceC539) = raw7934 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw7934; decide +kernel
    rw [ha]
    exact (canonical7934 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA539 + difference 0 3) (sourceB539 + difference 3 0) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA539 + difference 0 3) (sourceB539 + difference 3 0) sourceC539) = raw9239 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw9239; decide +kernel
    rw [ha]
    exact (canonical9239 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA539 + difference 0 4) (sourceB539 + difference 4 0) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3106) := by
    have ha : (tripleCharges (sourceA539 + difference 0 4) (sourceB539 + difference 4 0) sourceC539) = raw9052 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw9052; decide +kernel
    rw [ha]
    exact (canonical9052 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA539 + difference 0 5) (sourceB539 + difference 5 0) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3003) := by
    have ha : (tripleCharges (sourceA539 + difference 0 5) (sourceB539 + difference 5 0) sourceC539) = raw9240 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw9240; decide +kernel
    rw [ha]
    exact (canonical9240 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA539 + difference 1 0) (sourceB539 + difference 0 1) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA539 + difference 1 0) (sourceB539 + difference 0 1) sourceC539) = raw9241 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw9241; decide +kernel
    rw [ha]
    exact (canonical9241 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA539 + difference 1 2) (sourceB539 + difference 2 1) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA539 + difference 1 2) (sourceB539 + difference 2 1) sourceC539) = raw5689 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw5689; decide +kernel
    rw [ha]
    exact (canonical5689 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA539 + difference 1 3) (sourceB539 + difference 3 1) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA539 + difference 1 3) (sourceB539 + difference 3 1) sourceC539) = raw5690 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw5690; decide +kernel
    rw [ha]
    exact (canonical5690 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA539 + difference 1 4) (sourceB539 + difference 4 1) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2745) := by
    have ha : (tripleCharges (sourceA539 + difference 1 4) (sourceB539 + difference 4 1) sourceC539) = raw5691 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw5691; decide +kernel
    rw [ha]
    exact (canonical5691 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA539 + difference 1 5) (sourceB539 + difference 5 1) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2746) := by
    have ha : (tripleCharges (sourceA539 + difference 1 5) (sourceB539 + difference 5 1) sourceC539) = raw5692 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw5692; decide +kernel
    rw [ha]
    exact (canonical5692 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA539 + difference 2 0) (sourceB539 + difference 0 2) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA539 + difference 2 0) (sourceB539 + difference 0 2) sourceC539) = raw5699 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw5699; decide +kernel
    rw [ha]
    exact (canonical5699 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA539 + difference 2 1) (sourceB539 + difference 1 2) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA539 + difference 2 1) (sourceB539 + difference 1 2) sourceC539) = raw7249 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw7249; decide +kernel
    rw [ha]
    exact (canonical7249 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA539 + difference 2 3) (sourceB539 + difference 3 2) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA539 + difference 2 3) (sourceB539 + difference 3 2) sourceC539) = raw9242 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw9242; decide +kernel
    rw [ha]
    exact (canonical9242 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA539 + difference 2 4) (sourceB539 + difference 4 2) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA539 + difference 2 4) (sourceB539 + difference 4 2) sourceC539) = raw9058 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw9058; decide +kernel
    rw [ha]
    exact (canonical9058 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA539 + difference 2 5) (sourceB539 + difference 5 2) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA539 + difference 2 5) (sourceB539 + difference 5 2) sourceC539) = raw9243 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw9243; decide +kernel
    rw [ha]
    exact (canonical9243 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA539 + difference 3 0) (sourceB539 + difference 0 3) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA539 + difference 3 0) (sourceB539 + difference 0 3) sourceC539) = raw5704 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw5704; decide +kernel
    rw [ha]
    exact (canonical5704 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA539 + difference 3 1) (sourceB539 + difference 1 3) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA539 + difference 3 1) (sourceB539 + difference 1 3) sourceC539) = raw6742 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw6742; decide +kernel
    rw [ha]
    exact (canonical6742 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA539 + difference 3 2) (sourceB539 + difference 2 3) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA539 + difference 3 2) (sourceB539 + difference 2 3) sourceC539) = raw6737 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw6737; decide +kernel
    rw [ha]
    exact (canonical6737 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA539 + difference 3 4) (sourceB539 + difference 4 3) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA539 + difference 3 4) (sourceB539 + difference 4 3) sourceC539) = raw8579 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw8579; decide +kernel
    rw [ha]
    exact (canonical8579 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA539 + difference 3 5) (sourceB539 + difference 5 3) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA539 + difference 3 5) (sourceB539 + difference 5 3) sourceC539) = raw9244 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw9244; decide +kernel
    rw [ha]
    exact (canonical9244 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA539 + difference 4 0) (sourceB539 + difference 0 4) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA539 + difference 4 0) (sourceB539 + difference 0 4) sourceC539) = raw5709 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw5709; decide +kernel
    rw [ha]
    exact (canonical5709 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA539 + difference 4 1) (sourceB539 + difference 1 4) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA539 + difference 4 1) (sourceB539 + difference 1 4) sourceC539) = raw6401 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw6401; decide +kernel
    rw [ha]
    exact (canonical6401 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA539 + difference 4 2) (sourceB539 + difference 2 4) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA539 + difference 4 2) (sourceB539 + difference 2 4) sourceC539) = raw6397 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw6397; decide +kernel
    rw [ha]
    exact (canonical6397 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA539 + difference 4 3) (sourceB539 + difference 3 4) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA539 + difference 4 3) (sourceB539 + difference 3 4) sourceC539) = raw7536 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw7536; decide +kernel
    rw [ha]
    exact (canonical7536 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA539 + difference 4 5) (sourceB539 + difference 5 4) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA539 + difference 4 5) (sourceB539 + difference 5 4) sourceC539) = raw7537 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw7537; decide +kernel
    rw [ha]
    exact (canonical7537 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA539 + difference 5 0) (sourceB539 + difference 0 5) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA539 + difference 5 0) (sourceB539 + difference 0 5) sourceC539) = raw5714 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw5714; decide +kernel
    rw [ha]
    exact (canonical5714 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA539 + difference 5 1) (sourceB539 + difference 1 5) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA539 + difference 5 1) (sourceB539 + difference 1 5) sourceC539) = raw6740 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw6740; decide +kernel
    rw [ha]
    exact (canonical6740 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA539 + difference 5 2) (sourceB539 + difference 2 5) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA539 + difference 5 2) (sourceB539 + difference 2 5) sourceC539) = raw6735 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw6735; decide +kernel
    rw [ha]
    exact (canonical6735 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA539 + difference 5 3) (sourceB539 + difference 3 5) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA539 + difference 5 3) (sourceB539 + difference 3 5) sourceC539) = raw7243 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw7243; decide +kernel
    rw [ha]
    exact (canonical7243 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA539 + difference 5 4) (sourceB539 + difference 4 5) sourceC539) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA539 + difference 5 4) (sourceB539 + difference 4 5) sourceC539) = raw7244 := by
      apply Matrix.ext; unfold tripleCharges sourceA539 sourceB539 sourceC539 difference raw7244; decide +kernel
    rw [ha]
    exact (canonical7244 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA539 sourceB539 sourceC539
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm539, Integer.Sparse.eval]
  linarith only [hs]

def sourceA540 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB540 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC540 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm540 : Integer.Sparse Master := [(Sum.inr 2694, 1), (Sum.inr 2704, 1), (Sum.inr 2705, 1), (Sum.inr 2742, 2), (Sum.inr 3016, 2), (Sum.inr 3024, 2), (Sum.inr 3025, 2), (Sum.inr 3054, 2), (Sum.inr 3058, 1), (Sum.inr 3059, 1), (Sum.inr 3064, 1), (Sum.inr 3065, 1), (Sum.inr 3075, 1), (Sum.inr 3077, 2), (Sum.inr 3078, 1), (Sum.inr 3101, 2), (Sum.inr 3102, 2), (Sum.inr 3221, 1), (Sum.inr 3222, 2), (Sum.inr 3223, 1), (Sum.inr 3227, 1)]

theorem sourceEq540 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm540 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA540 + difference 0 1) (sourceB540 + difference 1 0) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA540 + difference 0 1) (sourceB540 + difference 1 0) sourceC540) = raw7260 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw7260; decide +kernel
    rw [ha]
    exact (canonical7260 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA540 + difference 0 2) (sourceB540 + difference 2 0) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA540 + difference 0 2) (sourceB540 + difference 2 0) sourceC540) = raw7947 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw7947; decide +kernel
    rw [ha]
    exact (canonical7947 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA540 + difference 0 3) (sourceB540 + difference 3 0) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA540 + difference 0 3) (sourceB540 + difference 3 0) sourceC540) = raw9245 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw9245; decide +kernel
    rw [ha]
    exact (canonical9245 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA540 + difference 0 4) (sourceB540 + difference 4 0) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA540 + difference 0 4) (sourceB540 + difference 4 0) sourceC540) = raw9064 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw9064; decide +kernel
    rw [ha]
    exact (canonical9064 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA540 + difference 0 5) (sourceB540 + difference 5 0) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA540 + difference 0 5) (sourceB540 + difference 5 0) sourceC540) = raw9246 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw9246; decide +kernel
    rw [ha]
    exact (canonical9246 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA540 + difference 1 0) (sourceB540 + difference 0 1) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA540 + difference 1 0) (sourceB540 + difference 0 1) sourceC540) = raw9247 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw9247; decide +kernel
    rw [ha]
    exact (canonical9247 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA540 + difference 1 2) (sourceB540 + difference 2 1) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA540 + difference 1 2) (sourceB540 + difference 2 1) sourceC540) = raw5719 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw5719; decide +kernel
    rw [ha]
    exact (canonical5719 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA540 + difference 1 3) (sourceB540 + difference 3 1) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA540 + difference 1 3) (sourceB540 + difference 3 1) sourceC540) = raw5720 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw5720; decide +kernel
    rw [ha]
    exact (canonical5720 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA540 + difference 1 4) (sourceB540 + difference 4 1) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA540 + difference 1 4) (sourceB540 + difference 4 1) sourceC540) = raw5721 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw5721; decide +kernel
    rw [ha]
    exact (canonical5721 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA540 + difference 1 5) (sourceB540 + difference 5 1) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA540 + difference 1 5) (sourceB540 + difference 5 1) sourceC540) = raw5722 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw5722; decide +kernel
    rw [ha]
    exact (canonical5722 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA540 + difference 2 0) (sourceB540 + difference 0 2) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA540 + difference 2 0) (sourceB540 + difference 0 2) sourceC540) = raw5729 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw5729; decide +kernel
    rw [ha]
    exact (canonical5729 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA540 + difference 2 1) (sourceB540 + difference 1 2) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA540 + difference 2 1) (sourceB540 + difference 1 2) sourceC540) = raw7267 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw7267; decide +kernel
    rw [ha]
    exact (canonical7267 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA540 + difference 2 3) (sourceB540 + difference 3 2) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA540 + difference 2 3) (sourceB540 + difference 3 2) sourceC540) = raw9248 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw9248; decide +kernel
    rw [ha]
    exact (canonical9248 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA540 + difference 2 4) (sourceB540 + difference 4 2) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA540 + difference 2 4) (sourceB540 + difference 4 2) sourceC540) = raw9070 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw9070; decide +kernel
    rw [ha]
    exact (canonical9070 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA540 + difference 2 5) (sourceB540 + difference 5 2) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA540 + difference 2 5) (sourceB540 + difference 5 2) sourceC540) = raw9249 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw9249; decide +kernel
    rw [ha]
    exact (canonical9249 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA540 + difference 3 0) (sourceB540 + difference 0 3) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA540 + difference 3 0) (sourceB540 + difference 0 3) sourceC540) = raw5734 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw5734; decide +kernel
    rw [ha]
    exact (canonical5734 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA540 + difference 3 1) (sourceB540 + difference 1 3) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA540 + difference 3 1) (sourceB540 + difference 1 3) sourceC540) = raw6770 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw6770; decide +kernel
    rw [ha]
    exact (canonical6770 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA540 + difference 3 2) (sourceB540 + difference 2 3) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA540 + difference 3 2) (sourceB540 + difference 2 3) sourceC540) = raw6765 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw6765; decide +kernel
    rw [ha]
    exact (canonical6765 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA540 + difference 3 4) (sourceB540 + difference 4 3) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA540 + difference 3 4) (sourceB540 + difference 4 3) sourceC540) = raw8596 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw8596; decide +kernel
    rw [ha]
    exact (canonical8596 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA540 + difference 3 5) (sourceB540 + difference 5 3) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA540 + difference 3 5) (sourceB540 + difference 5 3) sourceC540) = raw8798 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw8798; decide +kernel
    rw [ha]
    exact (canonical8798 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA540 + difference 4 0) (sourceB540 + difference 0 4) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA540 + difference 4 0) (sourceB540 + difference 0 4) sourceC540) = raw5739 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw5739; decide +kernel
    rw [ha]
    exact (canonical5739 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA540 + difference 4 1) (sourceB540 + difference 1 4) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA540 + difference 4 1) (sourceB540 + difference 1 4) sourceC540) = raw6423 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw6423; decide +kernel
    rw [ha]
    exact (canonical6423 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA540 + difference 4 2) (sourceB540 + difference 2 4) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA540 + difference 4 2) (sourceB540 + difference 2 4) sourceC540) = raw6419 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw6419; decide +kernel
    rw [ha]
    exact (canonical6419 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA540 + difference 4 3) (sourceB540 + difference 3 4) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA540 + difference 4 3) (sourceB540 + difference 3 4) sourceC540) = raw7545 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw7545; decide +kernel
    rw [ha]
    exact (canonical7545 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA540 + difference 4 5) (sourceB540 + difference 5 4) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA540 + difference 4 5) (sourceB540 + difference 5 4) sourceC540) = raw7546 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw7546; decide +kernel
    rw [ha]
    exact (canonical7546 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA540 + difference 5 0) (sourceB540 + difference 0 5) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA540 + difference 5 0) (sourceB540 + difference 0 5) sourceC540) = raw5744 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw5744; decide +kernel
    rw [ha]
    exact (canonical5744 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA540 + difference 5 1) (sourceB540 + difference 1 5) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA540 + difference 5 1) (sourceB540 + difference 1 5) sourceC540) = raw6768 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw6768; decide +kernel
    rw [ha]
    exact (canonical6768 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA540 + difference 5 2) (sourceB540 + difference 2 5) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA540 + difference 5 2) (sourceB540 + difference 2 5) sourceC540) = raw6763 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw6763; decide +kernel
    rw [ha]
    exact (canonical6763 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA540 + difference 5 3) (sourceB540 + difference 3 5) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA540 + difference 5 3) (sourceB540 + difference 3 5) sourceC540) = raw7261 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw7261; decide +kernel
    rw [ha]
    exact (canonical7261 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA540 + difference 5 4) (sourceB540 + difference 4 5) sourceC540) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA540 + difference 5 4) (sourceB540 + difference 4 5) sourceC540) = raw7262 := by
      apply Matrix.ext; unfold tripleCharges sourceA540 sourceB540 sourceC540 difference raw7262; decide +kernel
    rw [ha]
    exact (canonical7262 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA540 sourceB540 sourceC540
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm540, Integer.Sparse.eval]
  linarith only [hs]

def sourceA541 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB541 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC541 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm541 : Integer.Sparse Master := [(Sum.inr 2509, 1), (Sum.inr 3493, 1), (Sum.inr 3498, 1), (Sum.inr 3547, 2), (Sum.inr 3625, 1), (Sum.inr 4084, -1)]

theorem sourceEq541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm541 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA541 + difference 0 0) (sourceB541 + difference 0 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA541 + difference 0 0) (sourceB541 + difference 0 0) sourceC541) = raw5749 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw5749; decide +kernel
    rw [ha]
    exact (canonical5749 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA541 + difference 0 1) (sourceB541 + difference 1 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3493) := by
    have ha : (tripleCharges (sourceA541 + difference 0 1) (sourceB541 + difference 1 0) sourceC541) = raw7278 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw7278; decide +kernel
    rw [ha]
    exact (canonical7278 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA541 + difference 0 2) (sourceB541 + difference 2 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA541 + difference 0 2) (sourceB541 + difference 2 0) sourceC541) = raw7960 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw7960; decide +kernel
    rw [ha]
    exact (canonical7960 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA541 + difference 0 3) (sourceB541 + difference 3 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA541 + difference 0 3) (sourceB541 + difference 3 0) sourceC541) = raw9250 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw9250; decide +kernel
    rw [ha]
    exact (canonical9250 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA541 + difference 0 4) (sourceB541 + difference 4 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3498) := by
    have ha : (tripleCharges (sourceA541 + difference 0 4) (sourceB541 + difference 4 0) sourceC541) = raw9076 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw9076; decide +kernel
    rw [ha]
    exact (canonical9076 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA541 + difference 0 5) (sourceB541 + difference 5 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA541 + difference 0 5) (sourceB541 + difference 5 0) sourceC541) = raw9251 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw9251; decide +kernel
    rw [ha]
    exact (canonical9251 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA541 + sourceB541) sourceC541) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA541 + sourceB541) sourceC541) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA541 sourceB541 sourceC541 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA541 sourceB541 sourceC541
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm541, Integer.Sparse.eval]
  linarith only [hs]

def sourceA542 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB542 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC542 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm542 : Integer.Sparse Master := [(Sum.inr 4414, 1), (Sum.inr 4416, 1), (Sum.inr 4420, 2), (Sum.inr 4494, 1), (Sum.inr 4579, 1), (Sum.inr 4585, 1), (Sum.inr 4600, 2), (Sum.inr 5011, 1), (Sum.inr 5016, 2), (Sum.inr 5057, 2), (Sum.inr 5097, 1), (Sum.inr 5150, 2), (Sum.inr 5205, 2), (Sum.inr 5265, 1), (Sum.inr 5266, 2), (Sum.inr 5270, 2), (Sum.inr 5281, 1), (Sum.inr 5282, 1), (Sum.inr 5290, 2), (Sum.inr 5301, 1), (Sum.inr 5450, 1)]

theorem sourceEq542 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm542 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA542 + difference 0 1) (sourceB542 + difference 1 0) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA542 + difference 0 1) (sourceB542 + difference 1 0) sourceC542) = raw9252 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9252; decide +kernel
    rw [ha]
    exact (canonical9252 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA542 + difference 0 2) (sourceB542 + difference 2 0) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA542 + difference 0 2) (sourceB542 + difference 2 0) sourceC542) = raw9253 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9253; decide +kernel
    rw [ha]
    exact (canonical9253 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA542 + difference 0 3) (sourceB542 + difference 3 0) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA542 + difference 0 3) (sourceB542 + difference 3 0) sourceC542) = raw9254 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9254; decide +kernel
    rw [ha]
    exact (canonical9254 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA542 + difference 0 4) (sourceB542 + difference 4 0) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA542 + difference 0 4) (sourceB542 + difference 4 0) sourceC542) = raw9255 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9255; decide +kernel
    rw [ha]
    exact (canonical9255 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA542 + difference 0 5) (sourceB542 + difference 5 0) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA542 + difference 0 5) (sourceB542 + difference 5 0) sourceC542) = raw9256 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9256; decide +kernel
    rw [ha]
    exact (canonical9256 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA542 + difference 1 0) (sourceB542 + difference 0 1) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4579) := by
    have ha : (tripleCharges (sourceA542 + difference 1 0) (sourceB542 + difference 0 1) sourceC542) = raw9257 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9257; decide +kernel
    rw [ha]
    exact (canonical9257 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA542 + difference 1 2) (sourceB542 + difference 2 1) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5057) := by
    have ha : (tripleCharges (sourceA542 + difference 1 2) (sourceB542 + difference 2 1) sourceC542) = raw9258 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9258; decide +kernel
    rw [ha]
    exact (canonical9258 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA542 + difference 1 3) (sourceB542 + difference 3 1) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5057) := by
    have ha : (tripleCharges (sourceA542 + difference 1 3) (sourceB542 + difference 3 1) sourceC542) = raw9259 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9259; decide +kernel
    rw [ha]
    exact (canonical9259 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA542 + difference 1 4) (sourceB542 + difference 4 1) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5097) := by
    have ha : (tripleCharges (sourceA542 + difference 1 4) (sourceB542 + difference 4 1) sourceC542) = raw9260 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9260; decide +kernel
    rw [ha]
    exact (canonical9260 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA542 + difference 1 5) (sourceB542 + difference 5 1) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA542 + difference 1 5) (sourceB542 + difference 5 1) sourceC542) = raw9261 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9261; decide +kernel
    rw [ha]
    exact (canonical9261 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA542 + difference 2 0) (sourceB542 + difference 0 2) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA542 + difference 2 0) (sourceB542 + difference 0 2) sourceC542) = raw9262 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9262; decide +kernel
    rw [ha]
    exact (canonical9262 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA542 + difference 2 1) (sourceB542 + difference 1 2) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA542 + difference 2 1) (sourceB542 + difference 1 2) sourceC542) = raw9263 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9263; decide +kernel
    rw [ha]
    exact (canonical9263 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA542 + difference 2 3) (sourceB542 + difference 3 2) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA542 + difference 2 3) (sourceB542 + difference 3 2) sourceC542) = raw9264 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9264; decide +kernel
    rw [ha]
    exact (canonical9264 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA542 + difference 2 4) (sourceB542 + difference 4 2) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA542 + difference 2 4) (sourceB542 + difference 4 2) sourceC542) = raw9265 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9265; decide +kernel
    rw [ha]
    exact (canonical9265 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA542 + difference 2 5) (sourceB542 + difference 5 2) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA542 + difference 2 5) (sourceB542 + difference 5 2) sourceC542) = raw9266 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9266; decide +kernel
    rw [ha]
    exact (canonical9266 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA542 + difference 3 0) (sourceB542 + difference 0 3) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA542 + difference 3 0) (sourceB542 + difference 0 3) sourceC542) = raw9267 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9267; decide +kernel
    rw [ha]
    exact (canonical9267 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA542 + difference 3 1) (sourceB542 + difference 1 3) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA542 + difference 3 1) (sourceB542 + difference 1 3) sourceC542) = raw9268 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9268; decide +kernel
    rw [ha]
    exact (canonical9268 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA542 + difference 3 2) (sourceB542 + difference 2 3) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA542 + difference 3 2) (sourceB542 + difference 2 3) sourceC542) = raw9269 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9269; decide +kernel
    rw [ha]
    exact (canonical9269 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA542 + difference 3 4) (sourceB542 + difference 4 3) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA542 + difference 3 4) (sourceB542 + difference 4 3) sourceC542) = raw9270 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9270; decide +kernel
    rw [ha]
    exact (canonical9270 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA542 + difference 3 5) (sourceB542 + difference 5 3) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA542 + difference 3 5) (sourceB542 + difference 5 3) sourceC542) = raw9271 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9271; decide +kernel
    rw [ha]
    exact (canonical9271 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA542 + difference 4 0) (sourceB542 + difference 0 4) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4585) := by
    have ha : (tripleCharges (sourceA542 + difference 4 0) (sourceB542 + difference 0 4) sourceC542) = raw9272 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9272; decide +kernel
    rw [ha]
    exact (canonical9272 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA542 + difference 4 1) (sourceB542 + difference 1 4) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5011) := by
    have ha : (tripleCharges (sourceA542 + difference 4 1) (sourceB542 + difference 1 4) sourceC542) = raw9273 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9273; decide +kernel
    rw [ha]
    exact (canonical9273 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA542 + difference 4 2) (sourceB542 + difference 2 4) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5016) := by
    have ha : (tripleCharges (sourceA542 + difference 4 2) (sourceB542 + difference 2 4) sourceC542) = raw9274 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9274; decide +kernel
    rw [ha]
    exact (canonical9274 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA542 + difference 4 3) (sourceB542 + difference 3 4) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5016) := by
    have ha : (tripleCharges (sourceA542 + difference 4 3) (sourceB542 + difference 3 4) sourceC542) = raw9275 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9275; decide +kernel
    rw [ha]
    exact (canonical9275 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA542 + difference 4 5) (sourceB542 + difference 5 4) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA542 + difference 4 5) (sourceB542 + difference 5 4) sourceC542) = raw9276 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9276; decide +kernel
    rw [ha]
    exact (canonical9276 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA542 + difference 5 0) (sourceB542 + difference 0 5) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4416) := by
    have ha : (tripleCharges (sourceA542 + difference 5 0) (sourceB542 + difference 0 5) sourceC542) = raw9277 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9277; decide +kernel
    rw [ha]
    exact (canonical9277 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA542 + difference 5 1) (sourceB542 + difference 1 5) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4414) := by
    have ha : (tripleCharges (sourceA542 + difference 5 1) (sourceB542 + difference 1 5) sourceC542) = raw9278 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9278; decide +kernel
    rw [ha]
    exact (canonical9278 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA542 + difference 5 2) (sourceB542 + difference 2 5) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4420) := by
    have ha : (tripleCharges (sourceA542 + difference 5 2) (sourceB542 + difference 2 5) sourceC542) = raw9279 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9279; decide +kernel
    rw [ha]
    exact (canonical9279 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA542 + difference 5 3) (sourceB542 + difference 3 5) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4420) := by
    have ha : (tripleCharges (sourceA542 + difference 5 3) (sourceB542 + difference 3 5) sourceC542) = raw9280 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9280; decide +kernel
    rw [ha]
    exact (canonical9280 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA542 + difference 5 4) (sourceB542 + difference 4 5) sourceC542) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4494) := by
    have ha : (tripleCharges (sourceA542 + difference 5 4) (sourceB542 + difference 4 5) sourceC542) = raw9281 := by
      apply Matrix.ext; unfold tripleCharges sourceA542 sourceB542 sourceC542 difference raw9281; decide +kernel
    rw [ha]
    exact (canonical9281 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA542 sourceB542 sourceC542
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm542, Integer.Sparse.eval]
  linarith only [hs]

def sourceA543 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB543 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC543 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm543 : Integer.Sparse Master := [(Sum.inr 1197, 1), (Sum.inr 1199, 1), (Sum.inr 1204, 1), (Sum.inr 1234, 2), (Sum.inr 1593, 1), (Sum.inr 1603, 2), (Sum.inr 1700, 1), (Sum.inr 2851, 2), (Sum.inr 2855, 2), (Sum.inr 2879, 2), (Sum.inr 2912, 1), (Sum.inr 2923, 2), (Sum.inr 3058, 1), (Sum.inr 3074, 1), (Sum.inr 3075, 2), (Sum.inr 3078, 1), (Sum.inr 3099, 2), (Sum.inr 3526, 1), (Sum.inr 3535, 2), (Sum.inr 3619, 1), (Sum.inr 4029, 1)]

theorem sourceEq543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm543 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA543 + difference 0 1) (sourceB543 + difference 1 0) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA543 + difference 0 1) (sourceB543 + difference 1 0) sourceC543) = raw9282 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9282; decide +kernel
    rw [ha]
    exact (canonical9282 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA543 + difference 0 2) (sourceB543 + difference 2 0) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA543 + difference 0 2) (sourceB543 + difference 2 0) sourceC543) = raw9283 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9283; decide +kernel
    rw [ha]
    exact (canonical9283 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA543 + difference 0 3) (sourceB543 + difference 3 0) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA543 + difference 0 3) (sourceB543 + difference 3 0) sourceC543) = raw9284 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9284; decide +kernel
    rw [ha]
    exact (canonical9284 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA543 + difference 0 4) (sourceB543 + difference 4 0) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA543 + difference 0 4) (sourceB543 + difference 4 0) sourceC543) = raw9285 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9285; decide +kernel
    rw [ha]
    exact (canonical9285 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA543 + difference 0 5) (sourceB543 + difference 5 0) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA543 + difference 0 5) (sourceB543 + difference 5 0) sourceC543) = raw9286 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9286; decide +kernel
    rw [ha]
    exact (canonical9286 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA543 + difference 1 0) (sourceB543 + difference 0 1) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1197) := by
    have ha : (tripleCharges (sourceA543 + difference 1 0) (sourceB543 + difference 0 1) sourceC543) = raw9287 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9287; decide +kernel
    rw [ha]
    exact (canonical9287 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA543 + difference 1 2) (sourceB543 + difference 2 1) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2851) := by
    have ha : (tripleCharges (sourceA543 + difference 1 2) (sourceB543 + difference 2 1) sourceC543) = raw9288 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9288; decide +kernel
    rw [ha]
    exact (canonical9288 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA543 + difference 1 3) (sourceB543 + difference 3 1) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2851) := by
    have ha : (tripleCharges (sourceA543 + difference 1 3) (sourceB543 + difference 3 1) sourceC543) = raw9289 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9289; decide +kernel
    rw [ha]
    exact (canonical9289 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA543 + difference 1 4) (sourceB543 + difference 4 1) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA543 + difference 1 4) (sourceB543 + difference 4 1) sourceC543) = raw9290 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9290; decide +kernel
    rw [ha]
    exact (canonical9290 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA543 + difference 1 5) (sourceB543 + difference 5 1) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA543 + difference 1 5) (sourceB543 + difference 5 1) sourceC543) = raw9291 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9291; decide +kernel
    rw [ha]
    exact (canonical9291 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA543 + difference 2 0) (sourceB543 + difference 0 2) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA543 + difference 2 0) (sourceB543 + difference 0 2) sourceC543) = raw9292 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9292; decide +kernel
    rw [ha]
    exact (canonical9292 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA543 + difference 2 1) (sourceB543 + difference 1 2) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA543 + difference 2 1) (sourceB543 + difference 1 2) sourceC543) = raw9293 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9293; decide +kernel
    rw [ha]
    exact (canonical9293 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA543 + difference 2 3) (sourceB543 + difference 3 2) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA543 + difference 2 3) (sourceB543 + difference 3 2) sourceC543) = raw9294 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9294; decide +kernel
    rw [ha]
    exact (canonical9294 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA543 + difference 2 4) (sourceB543 + difference 4 2) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA543 + difference 2 4) (sourceB543 + difference 4 2) sourceC543) = raw9295 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9295; decide +kernel
    rw [ha]
    exact (canonical9295 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA543 + difference 2 5) (sourceB543 + difference 5 2) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA543 + difference 2 5) (sourceB543 + difference 5 2) sourceC543) = raw9296 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9296; decide +kernel
    rw [ha]
    exact (canonical9296 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA543 + difference 3 0) (sourceB543 + difference 0 3) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA543 + difference 3 0) (sourceB543 + difference 0 3) sourceC543) = raw9297 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9297; decide +kernel
    rw [ha]
    exact (canonical9297 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA543 + difference 3 1) (sourceB543 + difference 1 3) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA543 + difference 3 1) (sourceB543 + difference 1 3) sourceC543) = raw9298 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9298; decide +kernel
    rw [ha]
    exact (canonical9298 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA543 + difference 3 2) (sourceB543 + difference 2 3) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA543 + difference 3 2) (sourceB543 + difference 2 3) sourceC543) = raw9299 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9299; decide +kernel
    rw [ha]
    exact (canonical9299 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA543 + difference 3 4) (sourceB543 + difference 4 3) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA543 + difference 3 4) (sourceB543 + difference 4 3) sourceC543) = raw9300 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9300; decide +kernel
    rw [ha]
    exact (canonical9300 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA543 + difference 3 5) (sourceB543 + difference 5 3) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA543 + difference 3 5) (sourceB543 + difference 5 3) sourceC543) = raw9301 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9301; decide +kernel
    rw [ha]
    exact (canonical9301 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA543 + difference 4 0) (sourceB543 + difference 0 4) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1204) := by
    have ha : (tripleCharges (sourceA543 + difference 4 0) (sourceB543 + difference 0 4) sourceC543) = raw9302 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9302; decide +kernel
    rw [ha]
    exact (canonical9302 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA543 + difference 4 1) (sourceB543 + difference 1 4) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2912) := by
    have ha : (tripleCharges (sourceA543 + difference 4 1) (sourceB543 + difference 1 4) sourceC543) = raw9303 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9303; decide +kernel
    rw [ha]
    exact (canonical9303 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA543 + difference 4 2) (sourceB543 + difference 2 4) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2855) := by
    have ha : (tripleCharges (sourceA543 + difference 4 2) (sourceB543 + difference 2 4) sourceC543) = raw9304 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9304; decide +kernel
    rw [ha]
    exact (canonical9304 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA543 + difference 4 3) (sourceB543 + difference 3 4) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2855) := by
    have ha : (tripleCharges (sourceA543 + difference 4 3) (sourceB543 + difference 3 4) sourceC543) = raw9305 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9305; decide +kernel
    rw [ha]
    exact (canonical9305 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA543 + difference 4 5) (sourceB543 + difference 5 4) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA543 + difference 4 5) (sourceB543 + difference 5 4) sourceC543) = raw9306 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9306; decide +kernel
    rw [ha]
    exact (canonical9306 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA543 + difference 5 0) (sourceB543 + difference 0 5) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1199) := by
    have ha : (tripleCharges (sourceA543 + difference 5 0) (sourceB543 + difference 0 5) sourceC543) = raw9307 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9307; decide +kernel
    rw [ha]
    exact (canonical9307 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA543 + difference 5 1) (sourceB543 + difference 1 5) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1593) := by
    have ha : (tripleCharges (sourceA543 + difference 5 1) (sourceB543 + difference 1 5) sourceC543) = raw9308 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9308; decide +kernel
    rw [ha]
    exact (canonical9308 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA543 + difference 5 2) (sourceB543 + difference 2 5) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1603) := by
    have ha : (tripleCharges (sourceA543 + difference 5 2) (sourceB543 + difference 2 5) sourceC543) = raw9309 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9309; decide +kernel
    rw [ha]
    exact (canonical9309 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA543 + difference 5 3) (sourceB543 + difference 3 5) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1603) := by
    have ha : (tripleCharges (sourceA543 + difference 5 3) (sourceB543 + difference 3 5) sourceC543) = raw9310 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9310; decide +kernel
    rw [ha]
    exact (canonical9310 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA543 + difference 5 4) (sourceB543 + difference 4 5) sourceC543) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA543 + difference 5 4) (sourceB543 + difference 4 5) sourceC543) = raw9311 := by
      apply Matrix.ext; unfold tripleCharges sourceA543 sourceB543 sourceC543 difference raw9311; decide +kernel
    rw [ha]
    exact (canonical9311 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA543 sourceB543 sourceC543
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm543, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
