import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical66

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA448 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB448 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC448 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceForm448 : Integer.Sparse Master := [(Sum.inr 1272, 1), (Sum.inr 1433, 2), (Sum.inr 1436, 1), (Sum.inr 1437, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

theorem sourceEq448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm448 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA448 + difference 5 0) (sourceB448 + difference 0 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA448 + difference 5 0) (sourceB448 + difference 0 5) sourceC448) = raw8171 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8171; decide +kernel
    rw [ha]
    exact (canonical8171 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA448 + difference 5 1) (sourceB448 + difference 1 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1433) := by
    have ha : (tripleCharges (sourceA448 + difference 5 1) (sourceB448 + difference 1 5) sourceC448) = raw8179 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8179; decide +kernel
    rw [ha]
    exact (canonical8179 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA448 + difference 5 2) (sourceB448 + difference 2 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1433) := by
    have ha : (tripleCharges (sourceA448 + difference 5 2) (sourceB448 + difference 2 5) sourceC448) = raw8185 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8185; decide +kernel
    rw [ha]
    exact (canonical8185 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA448 + difference 5 3) (sourceB448 + difference 3 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1437) := by
    have ha : (tripleCharges (sourceA448 + difference 5 3) (sourceB448 + difference 3 5) sourceC448) = raw8182 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8182; decide +kernel
    rw [ha]
    exact (canonical8182 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA448 + difference 5 4) (sourceB448 + difference 4 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA448 + difference 5 4) (sourceB448 + difference 4 5) sourceC448) = raw8186 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8186; decide +kernel
    rw [ha]
    exact (canonical8186 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA448 + difference 5 5) (sourceB448 + difference 5 5) sourceC448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA448 + difference 5 5) (sourceB448 + difference 5 5) sourceC448) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA448 sourceB448 sourceC448 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA448 + sourceB448) sourceC448) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA448 + sourceB448) sourceC448) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA448 sourceB448 sourceC448 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA448 sourceB448 sourceC448
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm448, Integer.Sparse.eval]
  linarith only [hs]

def sourceA449 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB449 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC449 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm449 : Integer.Sparse Master := [(Sum.inr 4462, 2), (Sum.inr 4464, 1), (Sum.inr 4465, 1), (Sum.inr 4506, 1), (Sum.inr 4853, 2), (Sum.inr 4871, 1), (Sum.inr 4890, 1), (Sum.inr 5077, 2), (Sum.inr 5079, 2), (Sum.inr 5108, 2), (Sum.inr 5173, 2), (Sum.inr 5175, 2), (Sum.inr 5270, 2), (Sum.inr 5288, 2), (Sum.inr 5289, 2), (Sum.inr 5295, 1), (Sum.inr 5303, 1), (Sum.inr 5304, 2), (Sum.inr 5306, 1)]

theorem sourceEq449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm449 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA449 + difference 0 1) (sourceB449 + difference 1 0) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA449 + difference 0 1) (sourceB449 + difference 1 0) sourceC449) = raw8187 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8187; decide +kernel
    rw [ha]
    exact (canonical8187 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA449 + difference 0 2) (sourceB449 + difference 2 0) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA449 + difference 0 2) (sourceB449 + difference 2 0) sourceC449) = raw8188 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8188; decide +kernel
    rw [ha]
    exact (canonical8188 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA449 + difference 0 3) (sourceB449 + difference 3 0) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA449 + difference 0 3) (sourceB449 + difference 3 0) sourceC449) = raw8189 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8189; decide +kernel
    rw [ha]
    exact (canonical8189 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA449 + difference 0 4) (sourceB449 + difference 4 0) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA449 + difference 0 4) (sourceB449 + difference 4 0) sourceC449) = raw4652 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw4652; decide +kernel
    rw [ha]
    exact (canonical4652 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA449 + difference 0 5) (sourceB449 + difference 5 0) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA449 + difference 0 5) (sourceB449 + difference 5 0) sourceC449) = raw8190 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8190; decide +kernel
    rw [ha]
    exact (canonical8190 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA449 + difference 1 0) (sourceB449 + difference 0 1) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA449 + difference 1 0) (sourceB449 + difference 0 1) sourceC449) = raw8191 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8191; decide +kernel
    rw [ha]
    exact (canonical8191 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA449 + difference 1 2) (sourceB449 + difference 2 1) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5077) := by
    have ha : (tripleCharges (sourceA449 + difference 1 2) (sourceB449 + difference 2 1) sourceC449) = raw8192 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8192; decide +kernel
    rw [ha]
    exact (canonical8192 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA449 + difference 1 3) (sourceB449 + difference 3 1) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA449 + difference 1 3) (sourceB449 + difference 3 1) sourceC449) = raw8193 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8193; decide +kernel
    rw [ha]
    exact (canonical8193 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA449 + difference 1 4) (sourceB449 + difference 4 1) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA449 + difference 1 4) (sourceB449 + difference 4 1) sourceC449) = raw4657 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw4657; decide +kernel
    rw [ha]
    exact (canonical4657 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA449 + difference 1 5) (sourceB449 + difference 5 1) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA449 + difference 1 5) (sourceB449 + difference 5 1) sourceC449) = raw8194 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8194; decide +kernel
    rw [ha]
    exact (canonical8194 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA449 + difference 2 0) (sourceB449 + difference 0 2) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA449 + difference 2 0) (sourceB449 + difference 0 2) sourceC449) = raw8195 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8195; decide +kernel
    rw [ha]
    exact (canonical8195 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA449 + difference 2 1) (sourceB449 + difference 1 2) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5077) := by
    have ha : (tripleCharges (sourceA449 + difference 2 1) (sourceB449 + difference 1 2) sourceC449) = raw8196 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8196; decide +kernel
    rw [ha]
    exact (canonical8196 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA449 + difference 2 3) (sourceB449 + difference 3 2) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA449 + difference 2 3) (sourceB449 + difference 3 2) sourceC449) = raw8197 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8197; decide +kernel
    rw [ha]
    exact (canonical8197 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA449 + difference 2 4) (sourceB449 + difference 4 2) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA449 + difference 2 4) (sourceB449 + difference 4 2) sourceC449) = raw4662 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw4662; decide +kernel
    rw [ha]
    exact (canonical4662 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA449 + difference 2 5) (sourceB449 + difference 5 2) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA449 + difference 2 5) (sourceB449 + difference 5 2) sourceC449) = raw8198 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8198; decide +kernel
    rw [ha]
    exact (canonical8198 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA449 + difference 3 0) (sourceB449 + difference 0 3) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4506) := by
    have ha : (tripleCharges (sourceA449 + difference 3 0) (sourceB449 + difference 0 3) sourceC449) = raw8199 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8199; decide +kernel
    rw [ha]
    exact (canonical8199 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA449 + difference 3 1) (sourceB449 + difference 1 3) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5108) := by
    have ha : (tripleCharges (sourceA449 + difference 3 1) (sourceB449 + difference 1 3) sourceC449) = raw8200 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8200; decide +kernel
    rw [ha]
    exact (canonical8200 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA449 + difference 3 2) (sourceB449 + difference 2 3) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5108) := by
    have ha : (tripleCharges (sourceA449 + difference 3 2) (sourceB449 + difference 2 3) sourceC449) = raw8201 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8201; decide +kernel
    rw [ha]
    exact (canonical8201 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA449 + difference 3 4) (sourceB449 + difference 4 3) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA449 + difference 3 4) (sourceB449 + difference 4 3) sourceC449) = raw4667 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw4667; decide +kernel
    rw [ha]
    exact (canonical4667 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA449 + difference 3 5) (sourceB449 + difference 5 3) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5303) := by
    have ha : (tripleCharges (sourceA449 + difference 3 5) (sourceB449 + difference 5 3) sourceC449) = raw8202 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8202; decide +kernel
    rw [ha]
    exact (canonical8202 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA449 + difference 4 0) (sourceB449 + difference 0 4) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4465) := by
    have ha : (tripleCharges (sourceA449 + difference 4 0) (sourceB449 + difference 0 4) sourceC449) = raw8203 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8203; decide +kernel
    rw [ha]
    exact (canonical8203 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA449 + difference 4 1) (sourceB449 + difference 1 4) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5079) := by
    have ha : (tripleCharges (sourceA449 + difference 4 1) (sourceB449 + difference 1 4) sourceC449) = raw8204 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8204; decide +kernel
    rw [ha]
    exact (canonical8204 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA449 + difference 4 2) (sourceB449 + difference 2 4) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5079) := by
    have ha : (tripleCharges (sourceA449 + difference 4 2) (sourceB449 + difference 2 4) sourceC449) = raw8205 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8205; decide +kernel
    rw [ha]
    exact (canonical8205 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA449 + difference 4 3) (sourceB449 + difference 3 4) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA449 + difference 4 3) (sourceB449 + difference 3 4) sourceC449) = raw8206 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8206; decide +kernel
    rw [ha]
    exact (canonical8206 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA449 + difference 4 5) (sourceB449 + difference 5 4) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA449 + difference 4 5) (sourceB449 + difference 5 4) sourceC449) = raw8207 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8207; decide +kernel
    rw [ha]
    exact (canonical8207 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA449 + difference 5 0) (sourceB449 + difference 0 5) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA449 + difference 5 0) (sourceB449 + difference 0 5) sourceC449) = raw4668 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw4668; decide +kernel
    rw [ha]
    exact (canonical4668 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA449 + difference 5 1) (sourceB449 + difference 1 5) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA449 + difference 5 1) (sourceB449 + difference 1 5) sourceC449) = raw4669 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw4669; decide +kernel
    rw [ha]
    exact (canonical4669 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA449 + difference 5 2) (sourceB449 + difference 2 5) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA449 + difference 5 2) (sourceB449 + difference 2 5) sourceC449) = raw4670 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw4670; decide +kernel
    rw [ha]
    exact (canonical4670 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA449 + difference 5 3) (sourceB449 + difference 3 5) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA449 + difference 5 3) (sourceB449 + difference 3 5) sourceC449) = raw4671 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw4671; decide +kernel
    rw [ha]
    exact (canonical4671 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA449 + difference 5 4) (sourceB449 + difference 4 5) sourceC449) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA449 + difference 5 4) (sourceB449 + difference 4 5) sourceC449) = raw8208 := by
      apply Matrix.ext; unfold tripleCharges sourceA449 sourceB449 sourceC449 difference raw8208; decide +kernel
    rw [ha]
    exact (canonical8208 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA449 sourceB449 sourceC449
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm449, Integer.Sparse.eval]
  linarith only [hs]

def sourceA450 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB450 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC450 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm450 : Integer.Sparse Master := [(Sum.inr 1045, 2), (Sum.inr 1047, 1), (Sum.inr 1048, 1), (Sum.inr 1090, 1), (Sum.inr 2484, 2), (Sum.inr 2486, 2), (Sum.inr 2487, 2), (Sum.inr 2518, 2), (Sum.inr 2600, 2), (Sum.inr 2602, 1), (Sum.inr 2603, 1), (Sum.inr 2754, 2), (Sum.inr 2755, 1), (Sum.inr 2760, 2), (Sum.inr 2761, 1), (Sum.inr 2769, 1), (Sum.inr 2779, 1), (Sum.inr 2782, 1), (Sum.inr 3097, 2), (Sum.inr 3119, 1), (Sum.inr 3120, 1)]

theorem sourceEq450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm450 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA450 + difference 0 1) (sourceB450 + difference 1 0) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA450 + difference 0 1) (sourceB450 + difference 1 0) sourceC450) = raw8209 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8209; decide +kernel
    rw [ha]
    exact (canonical8209 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA450 + difference 0 2) (sourceB450 + difference 2 0) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA450 + difference 0 2) (sourceB450 + difference 2 0) sourceC450) = raw8210 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8210; decide +kernel
    rw [ha]
    exact (canonical8210 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA450 + difference 0 3) (sourceB450 + difference 3 0) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA450 + difference 0 3) (sourceB450 + difference 3 0) sourceC450) = raw8211 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8211; decide +kernel
    rw [ha]
    exact (canonical8211 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA450 + difference 0 4) (sourceB450 + difference 4 0) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA450 + difference 0 4) (sourceB450 + difference 4 0) sourceC450) = raw4682 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw4682; decide +kernel
    rw [ha]
    exact (canonical4682 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA450 + difference 0 5) (sourceB450 + difference 5 0) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA450 + difference 0 5) (sourceB450 + difference 5 0) sourceC450) = raw8212 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8212; decide +kernel
    rw [ha]
    exact (canonical8212 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA450 + difference 1 0) (sourceB450 + difference 0 1) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA450 + difference 1 0) (sourceB450 + difference 0 1) sourceC450) = raw8213 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8213; decide +kernel
    rw [ha]
    exact (canonical8213 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA450 + difference 1 2) (sourceB450 + difference 2 1) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2484) := by
    have ha : (tripleCharges (sourceA450 + difference 1 2) (sourceB450 + difference 2 1) sourceC450) = raw8214 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8214; decide +kernel
    rw [ha]
    exact (canonical8214 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA450 + difference 1 3) (sourceB450 + difference 3 1) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA450 + difference 1 3) (sourceB450 + difference 3 1) sourceC450) = raw8215 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8215; decide +kernel
    rw [ha]
    exact (canonical8215 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA450 + difference 1 4) (sourceB450 + difference 4 1) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA450 + difference 1 4) (sourceB450 + difference 4 1) sourceC450) = raw4687 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw4687; decide +kernel
    rw [ha]
    exact (canonical4687 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA450 + difference 1 5) (sourceB450 + difference 5 1) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA450 + difference 1 5) (sourceB450 + difference 5 1) sourceC450) = raw8216 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8216; decide +kernel
    rw [ha]
    exact (canonical8216 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA450 + difference 2 0) (sourceB450 + difference 0 2) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA450 + difference 2 0) (sourceB450 + difference 0 2) sourceC450) = raw8217 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8217; decide +kernel
    rw [ha]
    exact (canonical8217 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA450 + difference 2 1) (sourceB450 + difference 1 2) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2484) := by
    have ha : (tripleCharges (sourceA450 + difference 2 1) (sourceB450 + difference 1 2) sourceC450) = raw8218 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8218; decide +kernel
    rw [ha]
    exact (canonical8218 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA450 + difference 2 3) (sourceB450 + difference 3 2) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA450 + difference 2 3) (sourceB450 + difference 3 2) sourceC450) = raw8219 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8219; decide +kernel
    rw [ha]
    exact (canonical8219 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA450 + difference 2 4) (sourceB450 + difference 4 2) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA450 + difference 2 4) (sourceB450 + difference 4 2) sourceC450) = raw4692 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw4692; decide +kernel
    rw [ha]
    exact (canonical4692 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA450 + difference 2 5) (sourceB450 + difference 5 2) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA450 + difference 2 5) (sourceB450 + difference 5 2) sourceC450) = raw8220 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8220; decide +kernel
    rw [ha]
    exact (canonical8220 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA450 + difference 3 0) (sourceB450 + difference 0 3) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1090) := by
    have ha : (tripleCharges (sourceA450 + difference 3 0) (sourceB450 + difference 0 3) sourceC450) = raw8221 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8221; decide +kernel
    rw [ha]
    exact (canonical8221 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA450 + difference 3 1) (sourceB450 + difference 1 3) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2518) := by
    have ha : (tripleCharges (sourceA450 + difference 3 1) (sourceB450 + difference 1 3) sourceC450) = raw8222 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8222; decide +kernel
    rw [ha]
    exact (canonical8222 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA450 + difference 3 2) (sourceB450 + difference 2 3) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2518) := by
    have ha : (tripleCharges (sourceA450 + difference 3 2) (sourceB450 + difference 2 3) sourceC450) = raw8223 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8223; decide +kernel
    rw [ha]
    exact (canonical8223 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA450 + difference 3 4) (sourceB450 + difference 4 3) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA450 + difference 3 4) (sourceB450 + difference 4 3) sourceC450) = raw4697 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw4697; decide +kernel
    rw [ha]
    exact (canonical4697 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA450 + difference 3 5) (sourceB450 + difference 5 3) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2779) := by
    have ha : (tripleCharges (sourceA450 + difference 3 5) (sourceB450 + difference 5 3) sourceC450) = raw8224 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8224; decide +kernel
    rw [ha]
    exact (canonical8224 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA450 + difference 4 0) (sourceB450 + difference 0 4) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1048) := by
    have ha : (tripleCharges (sourceA450 + difference 4 0) (sourceB450 + difference 0 4) sourceC450) = raw8225 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8225; decide +kernel
    rw [ha]
    exact (canonical8225 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA450 + difference 4 1) (sourceB450 + difference 1 4) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2487) := by
    have ha : (tripleCharges (sourceA450 + difference 4 1) (sourceB450 + difference 1 4) sourceC450) = raw8226 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8226; decide +kernel
    rw [ha]
    exact (canonical8226 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA450 + difference 4 2) (sourceB450 + difference 2 4) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2487) := by
    have ha : (tripleCharges (sourceA450 + difference 4 2) (sourceB450 + difference 2 4) sourceC450) = raw8227 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8227; decide +kernel
    rw [ha]
    exact (canonical8227 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA450 + difference 4 3) (sourceB450 + difference 3 4) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2603) := by
    have ha : (tripleCharges (sourceA450 + difference 4 3) (sourceB450 + difference 3 4) sourceC450) = raw8228 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8228; decide +kernel
    rw [ha]
    exact (canonical8228 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA450 + difference 4 5) (sourceB450 + difference 5 4) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA450 + difference 4 5) (sourceB450 + difference 5 4) sourceC450) = raw8229 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8229; decide +kernel
    rw [ha]
    exact (canonical8229 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA450 + difference 5 0) (sourceB450 + difference 0 5) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA450 + difference 5 0) (sourceB450 + difference 0 5) sourceC450) = raw4698 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw4698; decide +kernel
    rw [ha]
    exact (canonical4698 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA450 + difference 5 1) (sourceB450 + difference 1 5) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA450 + difference 5 1) (sourceB450 + difference 1 5) sourceC450) = raw4699 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw4699; decide +kernel
    rw [ha]
    exact (canonical4699 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA450 + difference 5 2) (sourceB450 + difference 2 5) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA450 + difference 5 2) (sourceB450 + difference 2 5) sourceC450) = raw4700 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw4700; decide +kernel
    rw [ha]
    exact (canonical4700 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA450 + difference 5 3) (sourceB450 + difference 3 5) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2602) := by
    have ha : (tripleCharges (sourceA450 + difference 5 3) (sourceB450 + difference 3 5) sourceC450) = raw4701 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw4701; decide +kernel
    rw [ha]
    exact (canonical4701 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA450 + difference 5 4) (sourceB450 + difference 4 5) sourceC450) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA450 + difference 5 4) (sourceB450 + difference 4 5) sourceC450) = raw8230 := by
      apply Matrix.ext; unfold tripleCharges sourceA450 sourceB450 sourceC450 difference raw8230; decide +kernel
    rw [ha]
    exact (canonical8230 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA450 sourceB450 sourceC450
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm450, Integer.Sparse.eval]
  linarith only [hs]

def sourceA451 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB451 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC451 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm451 : Integer.Sparse Master := [(Sum.inr 1656, 2), (Sum.inr 1657, 1), (Sum.inr 1661, 1), (Sum.inr 1745, 1), (Sum.inr 2259, 2), (Sum.inr 2287, 1), (Sum.inr 2290, 1), (Sum.inr 2584, 2), (Sum.inr 2603, 1), (Sum.inr 2717, 2), (Sum.inr 2735, 2), (Sum.inr 2738, 2), (Sum.inr 2761, 1), (Sum.inr 2762, 2), (Sum.inr 2763, 2), (Sum.inr 2781, 1), (Sum.inr 2782, 1), (Sum.inr 2784, 1), (Sum.inr 3096, 2), (Sum.inr 3118, 1), (Sum.inr 3119, 1)]

theorem sourceEq451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm451 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA451 + difference 0 1) (sourceB451 + difference 1 0) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA451 + difference 0 1) (sourceB451 + difference 1 0) sourceC451) = raw8231 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8231; decide +kernel
    rw [ha]
    exact (canonical8231 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA451 + difference 0 2) (sourceB451 + difference 2 0) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA451 + difference 0 2) (sourceB451 + difference 2 0) sourceC451) = raw8232 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8232; decide +kernel
    rw [ha]
    exact (canonical8232 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA451 + difference 0 3) (sourceB451 + difference 3 0) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA451 + difference 0 3) (sourceB451 + difference 3 0) sourceC451) = raw8233 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8233; decide +kernel
    rw [ha]
    exact (canonical8233 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA451 + difference 0 4) (sourceB451 + difference 4 0) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA451 + difference 0 4) (sourceB451 + difference 4 0) sourceC451) = raw4712 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw4712; decide +kernel
    rw [ha]
    exact (canonical4712 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA451 + difference 0 5) (sourceB451 + difference 5 0) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA451 + difference 0 5) (sourceB451 + difference 5 0) sourceC451) = raw8234 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8234; decide +kernel
    rw [ha]
    exact (canonical8234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA451 + difference 1 0) (sourceB451 + difference 0 1) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA451 + difference 1 0) (sourceB451 + difference 0 1) sourceC451) = raw8235 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8235; decide +kernel
    rw [ha]
    exact (canonical8235 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA451 + difference 1 2) (sourceB451 + difference 2 1) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2717) := by
    have ha : (tripleCharges (sourceA451 + difference 1 2) (sourceB451 + difference 2 1) sourceC451) = raw8236 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8236; decide +kernel
    rw [ha]
    exact (canonical8236 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA451 + difference 1 3) (sourceB451 + difference 3 1) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA451 + difference 1 3) (sourceB451 + difference 3 1) sourceC451) = raw8237 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8237; decide +kernel
    rw [ha]
    exact (canonical8237 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA451 + difference 1 4) (sourceB451 + difference 4 1) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA451 + difference 1 4) (sourceB451 + difference 4 1) sourceC451) = raw4717 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw4717; decide +kernel
    rw [ha]
    exact (canonical4717 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA451 + difference 1 5) (sourceB451 + difference 5 1) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA451 + difference 1 5) (sourceB451 + difference 5 1) sourceC451) = raw8238 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8238; decide +kernel
    rw [ha]
    exact (canonical8238 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA451 + difference 2 0) (sourceB451 + difference 0 2) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA451 + difference 2 0) (sourceB451 + difference 0 2) sourceC451) = raw8239 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8239; decide +kernel
    rw [ha]
    exact (canonical8239 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA451 + difference 2 1) (sourceB451 + difference 1 2) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2717) := by
    have ha : (tripleCharges (sourceA451 + difference 2 1) (sourceB451 + difference 1 2) sourceC451) = raw8240 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8240; decide +kernel
    rw [ha]
    exact (canonical8240 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA451 + difference 2 3) (sourceB451 + difference 3 2) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA451 + difference 2 3) (sourceB451 + difference 3 2) sourceC451) = raw8241 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8241; decide +kernel
    rw [ha]
    exact (canonical8241 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA451 + difference 2 4) (sourceB451 + difference 4 2) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA451 + difference 2 4) (sourceB451 + difference 4 2) sourceC451) = raw4722 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw4722; decide +kernel
    rw [ha]
    exact (canonical4722 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA451 + difference 2 5) (sourceB451 + difference 5 2) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA451 + difference 2 5) (sourceB451 + difference 5 2) sourceC451) = raw8242 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8242; decide +kernel
    rw [ha]
    exact (canonical8242 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA451 + difference 3 0) (sourceB451 + difference 0 3) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1661) := by
    have ha : (tripleCharges (sourceA451 + difference 3 0) (sourceB451 + difference 0 3) sourceC451) = raw8243 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8243; decide +kernel
    rw [ha]
    exact (canonical8243 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA451 + difference 3 1) (sourceB451 + difference 1 3) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2762) := by
    have ha : (tripleCharges (sourceA451 + difference 3 1) (sourceB451 + difference 1 3) sourceC451) = raw8244 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8244; decide +kernel
    rw [ha]
    exact (canonical8244 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA451 + difference 3 2) (sourceB451 + difference 2 3) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2762) := by
    have ha : (tripleCharges (sourceA451 + difference 3 2) (sourceB451 + difference 2 3) sourceC451) = raw8245 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8245; decide +kernel
    rw [ha]
    exact (canonical8245 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA451 + difference 3 4) (sourceB451 + difference 4 3) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA451 + difference 3 4) (sourceB451 + difference 4 3) sourceC451) = raw4727 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw4727; decide +kernel
    rw [ha]
    exact (canonical4727 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA451 + difference 3 5) (sourceB451 + difference 5 3) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3118) := by
    have ha : (tripleCharges (sourceA451 + difference 3 5) (sourceB451 + difference 5 3) sourceC451) = raw8246 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8246; decide +kernel
    rw [ha]
    exact (canonical8246 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA451 + difference 4 0) (sourceB451 + difference 0 4) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1657) := by
    have ha : (tripleCharges (sourceA451 + difference 4 0) (sourceB451 + difference 0 4) sourceC451) = raw8247 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8247; decide +kernel
    rw [ha]
    exact (canonical8247 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA451 + difference 4 1) (sourceB451 + difference 1 4) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2584) := by
    have ha : (tripleCharges (sourceA451 + difference 4 1) (sourceB451 + difference 1 4) sourceC451) = raw8248 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8248; decide +kernel
    rw [ha]
    exact (canonical8248 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA451 + difference 4 2) (sourceB451 + difference 2 4) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2584) := by
    have ha : (tripleCharges (sourceA451 + difference 4 2) (sourceB451 + difference 2 4) sourceC451) = raw8249 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8249; decide +kernel
    rw [ha]
    exact (canonical8249 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA451 + difference 4 3) (sourceB451 + difference 3 4) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA451 + difference 4 3) (sourceB451 + difference 3 4) sourceC451) = raw8250 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8250; decide +kernel
    rw [ha]
    exact (canonical8250 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA451 + difference 4 5) (sourceB451 + difference 5 4) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2603) := by
    have ha : (tripleCharges (sourceA451 + difference 4 5) (sourceB451 + difference 5 4) sourceC451) = raw8251 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8251; decide +kernel
    rw [ha]
    exact (canonical8251 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA451 + difference 5 0) (sourceB451 + difference 0 5) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA451 + difference 5 0) (sourceB451 + difference 0 5) sourceC451) = raw4728 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw4728; decide +kernel
    rw [ha]
    exact (canonical4728 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA451 + difference 5 1) (sourceB451 + difference 1 5) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA451 + difference 5 1) (sourceB451 + difference 1 5) sourceC451) = raw4729 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw4729; decide +kernel
    rw [ha]
    exact (canonical4729 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA451 + difference 5 2) (sourceB451 + difference 2 5) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA451 + difference 5 2) (sourceB451 + difference 2 5) sourceC451) = raw4730 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw4730; decide +kernel
    rw [ha]
    exact (canonical4730 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA451 + difference 5 3) (sourceB451 + difference 3 5) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA451 + difference 5 3) (sourceB451 + difference 3 5) sourceC451) = raw4731 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw4731; decide +kernel
    rw [ha]
    exact (canonical4731 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA451 + difference 5 4) (sourceB451 + difference 4 5) sourceC451) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA451 + difference 5 4) (sourceB451 + difference 4 5) sourceC451) = raw8252 := by
      apply Matrix.ext; unfold tripleCharges sourceA451 sourceB451 sourceC451 difference raw8252; decide +kernel
    rw [ha]
    exact (canonical8252 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA451 sourceB451 sourceC451
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm451, Integer.Sparse.eval]
  linarith only [hs]

def sourceA452 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB452 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC452 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm452 : Integer.Sparse Master := [(Sum.inr 3098, 1), (Sum.inr 3572, 2), (Sum.inr 3583, 2), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

theorem sourceEq452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm452 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA452 + difference 0 0) (sourceB452 + difference 0 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA452 + difference 0 0) (sourceB452 + difference 0 0) sourceC452) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA452 + difference 0 1) (sourceB452 + difference 1 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA452 + difference 0 1) (sourceB452 + difference 1 0) sourceC452) = raw8254 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw8254; decide +kernel
    rw [ha]
    exact (canonical8254 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA452 + difference 0 2) (sourceB452 + difference 2 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA452 + difference 0 2) (sourceB452 + difference 2 0) sourceC452) = raw8255 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw8255; decide +kernel
    rw [ha]
    exact (canonical8255 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA452 + difference 0 3) (sourceB452 + difference 3 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA452 + difference 0 3) (sourceB452 + difference 3 0) sourceC452) = raw8256 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw8256; decide +kernel
    rw [ha]
    exact (canonical8256 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA452 + difference 0 4) (sourceB452 + difference 4 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3623) := by
    have ha : (tripleCharges (sourceA452 + difference 0 4) (sourceB452 + difference 4 0) sourceC452) = raw4743 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw4743; decide +kernel
    rw [ha]
    exact (canonical4743 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA452 + difference 0 5) (sourceB452 + difference 5 0) sourceC452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA452 + difference 0 5) (sourceB452 + difference 5 0) sourceC452) = raw8257 := by
      apply Matrix.ext; unfold tripleCharges sourceA452 sourceB452 sourceC452 difference raw8257; decide +kernel
    rw [ha]
    exact (canonical8257 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA452 + sourceB452) sourceC452) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA452 + sourceB452) sourceC452) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA452 sourceB452 sourceC452 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA452 sourceB452 sourceC452
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm452, Integer.Sparse.eval]
  linarith only [hs]

def sourceA453 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB453 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC453 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm453 : Integer.Sparse Master := [(Sum.inr 1404, 2), (Sum.inr 1408, 1), (Sum.inr 1418, 1), (Sum.inr 1440, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

theorem sourceEq453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm453 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA453 + difference 0 0) (sourceB453 + difference 0 0) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA453 + difference 0 0) (sourceB453 + difference 0 0) sourceC453) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA453 + difference 1 0) (sourceB453 + difference 0 1) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1404) := by
    have ha : (tripleCharges (sourceA453 + difference 1 0) (sourceB453 + difference 0 1) sourceC453) = raw8258 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw8258; decide +kernel
    rw [ha]
    exact (canonical8258 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA453 + difference 2 0) (sourceB453 + difference 0 2) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1404) := by
    have ha : (tripleCharges (sourceA453 + difference 2 0) (sourceB453 + difference 0 2) sourceC453) = raw8259 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw8259; decide +kernel
    rw [ha]
    exact (canonical8259 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA453 + difference 3 0) (sourceB453 + difference 0 3) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1440) := by
    have ha : (tripleCharges (sourceA453 + difference 3 0) (sourceB453 + difference 0 3) sourceC453) = raw8260 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw8260; decide +kernel
    rw [ha]
    exact (canonical8260 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA453 + difference 4 0) (sourceB453 + difference 0 4) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1418) := by
    have ha : (tripleCharges (sourceA453 + difference 4 0) (sourceB453 + difference 0 4) sourceC453) = raw8261 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw8261; decide +kernel
    rw [ha]
    exact (canonical8261 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA453 + difference 5 0) (sourceB453 + difference 0 5) sourceC453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA453 + difference 5 0) (sourceB453 + difference 0 5) sourceC453) = raw4748 := by
      apply Matrix.ext; unfold tripleCharges sourceA453 sourceB453 sourceC453 difference raw4748; decide +kernel
    rw [ha]
    exact (canonical4748 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA453 + sourceB453) sourceC453) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA453 + sourceB453) sourceC453) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA453 sourceB453 sourceC453 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA453 sourceB453 sourceC453
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm453, Integer.Sparse.eval]
  linarith only [hs]

def sourceA454 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB454 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC454 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm454 : Integer.Sparse Master := [(Sum.inr 1404, 1), (Sum.inr 2952, 1), (Sum.inr 2983, 1), (Sum.inr 3075, 1), (Sum.inr 3096, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

theorem sourceEq454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm454 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA454 + difference 1 0) (sourceB454 + difference 0 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1404) := by
    have ha : (tripleCharges (sourceA454 + difference 1 0) (sourceB454 + difference 0 1) sourceC454) = raw8258 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw8258; decide +kernel
    rw [ha]
    exact (canonical8258 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA454 + difference 1 1) (sourceB454 + difference 1 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA454 + difference 1 1) (sourceB454 + difference 1 1) sourceC454) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA454 + difference 1 2) (sourceB454 + difference 2 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2983) := by
    have ha : (tripleCharges (sourceA454 + difference 1 2) (sourceB454 + difference 2 1) sourceC454) = raw8262 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw8262; decide +kernel
    rw [ha]
    exact (canonical8262 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA454 + difference 1 3) (sourceB454 + difference 3 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA454 + difference 1 3) (sourceB454 + difference 3 1) sourceC454) = raw8263 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw8263; decide +kernel
    rw [ha]
    exact (canonical8263 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA454 + difference 1 4) (sourceB454 + difference 4 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA454 + difference 1 4) (sourceB454 + difference 4 1) sourceC454) = raw4753 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw4753; decide +kernel
    rw [ha]
    exact (canonical4753 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA454 + difference 1 5) (sourceB454 + difference 5 1) sourceC454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA454 + difference 1 5) (sourceB454 + difference 5 1) sourceC454) = raw8264 := by
      apply Matrix.ext; unfold tripleCharges sourceA454 sourceB454 sourceC454 difference raw8264; decide +kernel
    rw [ha]
    exact (canonical8264 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA454 + sourceB454) sourceC454) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA454 + sourceB454) sourceC454) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA454 sourceB454 sourceC454 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA454 sourceB454 sourceC454
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm454, Integer.Sparse.eval]
  linarith only [hs]

def sourceA455 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB455 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC455 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm455 : Integer.Sparse Master := [(Sum.inr 2090, 1), (Sum.inr 2962, 1), (Sum.inr 2983, 1), (Sum.inr 2995, 1), (Sum.inr 3098, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

theorem sourceEq455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm455 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA455 + difference 0 1) (sourceB455 + difference 1 0) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA455 + difference 0 1) (sourceB455 + difference 1 0) sourceC455) = raw8254 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw8254; decide +kernel
    rw [ha]
    exact (canonical8254 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA455 + difference 1 1) (sourceB455 + difference 1 1) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA455 + difference 1 1) (sourceB455 + difference 1 1) sourceC455) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA455 + difference 2 1) (sourceB455 + difference 1 2) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2983) := by
    have ha : (tripleCharges (sourceA455 + difference 2 1) (sourceB455 + difference 1 2) sourceC455) = raw8265 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw8265; decide +kernel
    rw [ha]
    exact (canonical8265 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA455 + difference 3 1) (sourceB455 + difference 1 3) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2995) := by
    have ha : (tripleCharges (sourceA455 + difference 3 1) (sourceB455 + difference 1 3) sourceC455) = raw8266 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw8266; decide +kernel
    rw [ha]
    exact (canonical8266 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA455 + difference 4 1) (sourceB455 + difference 1 4) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2962) := by
    have ha : (tripleCharges (sourceA455 + difference 4 1) (sourceB455 + difference 1 4) sourceC455) = raw8267 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw8267; decide +kernel
    rw [ha]
    exact (canonical8267 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA455 + difference 5 1) (sourceB455 + difference 1 5) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA455 + difference 5 1) (sourceB455 + difference 1 5) sourceC455) = raw4756 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw4756; decide +kernel
    rw [ha]
    exact (canonical4756 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA455 + sourceB455) sourceC455) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA455 + sourceB455) sourceC455) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA455 sourceB455 sourceC455 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA455 sourceB455 sourceC455
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm455, Integer.Sparse.eval]
  linarith only [hs]

def sourceA456 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB456 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC456 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm456 : Integer.Sparse Master := [(Sum.inr 1440, 1), (Sum.inr 2995, 2), (Sum.inr 3098, 2), (Sum.inr 3118, 1), (Sum.inr 4083, -1)]

theorem sourceEq456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm456 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA456 + difference 3 0) (sourceB456 + difference 0 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1440) := by
    have ha : (tripleCharges (sourceA456 + difference 3 0) (sourceB456 + difference 0 3) sourceC456) = raw8260 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw8260; decide +kernel
    rw [ha]
    exact (canonical8260 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA456 + difference 3 1) (sourceB456 + difference 1 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2995) := by
    have ha : (tripleCharges (sourceA456 + difference 3 1) (sourceB456 + difference 1 3) sourceC456) = raw8266 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw8266; decide +kernel
    rw [ha]
    exact (canonical8266 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA456 + difference 3 2) (sourceB456 + difference 2 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2995) := by
    have ha : (tripleCharges (sourceA456 + difference 3 2) (sourceB456 + difference 2 3) sourceC456) = raw8268 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw8268; decide +kernel
    rw [ha]
    exact (canonical8268 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA456 + difference 3 3) (sourceB456 + difference 3 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA456 + difference 3 3) (sourceB456 + difference 3 3) sourceC456) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA456 + difference 3 4) (sourceB456 + difference 4 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA456 + difference 3 4) (sourceB456 + difference 4 3) sourceC456) = raw4760 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw4760; decide +kernel
    rw [ha]
    exact (canonical4760 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA456 + difference 3 5) (sourceB456 + difference 5 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3118) := by
    have ha : (tripleCharges (sourceA456 + difference 3 5) (sourceB456 + difference 5 3) sourceC456) = raw8269 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw8269; decide +kernel
    rw [ha]
    exact (canonical8269 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA456 + sourceB456) sourceC456) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA456 + sourceB456) sourceC456) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA456 sourceB456 sourceC456 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA456 sourceB456 sourceC456
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm456, Integer.Sparse.eval]
  linarith only [hs]

def sourceA457 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB457 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC457 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm457 : Integer.Sparse Master := [(Sum.inr 2112, 1), (Sum.inr 2952, 2), (Sum.inr 2967, 1), (Sum.inr 3098, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

theorem sourceEq457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm457 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA457 + difference 0 3) (sourceB457 + difference 3 0) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA457 + difference 0 3) (sourceB457 + difference 3 0) sourceC457) = raw8256 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw8256; decide +kernel
    rw [ha]
    exact (canonical8256 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA457 + difference 1 3) (sourceB457 + difference 3 1) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA457 + difference 1 3) (sourceB457 + difference 3 1) sourceC457) = raw8263 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw8263; decide +kernel
    rw [ha]
    exact (canonical8263 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA457 + difference 2 3) (sourceB457 + difference 3 2) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA457 + difference 2 3) (sourceB457 + difference 3 2) sourceC457) = raw8270 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw8270; decide +kernel
    rw [ha]
    exact (canonical8270 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA457 + difference 3 3) (sourceB457 + difference 3 3) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA457 + difference 3 3) (sourceB457 + difference 3 3) sourceC457) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA457 + difference 4 3) (sourceB457 + difference 3 4) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA457 + difference 4 3) (sourceB457 + difference 3 4) sourceC457) = raw8271 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw8271; decide +kernel
    rw [ha]
    exact (canonical8271 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA457 + difference 5 3) (sourceB457 + difference 3 5) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA457 + difference 5 3) (sourceB457 + difference 3 5) sourceC457) = raw4762 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw4762; decide +kernel
    rw [ha]
    exact (canonical4762 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA457 + sourceB457) sourceC457) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA457 + sourceB457) sourceC457) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA457 sourceB457 sourceC457 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA457 sourceB457 sourceC457
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm457, Integer.Sparse.eval]
  linarith only [hs]

def sourceA458 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB458 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC458 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm458 : Integer.Sparse Master := [(Sum.inr 1418, 1), (Sum.inr 2962, 2), (Sum.inr 2967, 2), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

theorem sourceEq458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm458 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA458 + difference 4 0) (sourceB458 + difference 0 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1418) := by
    have ha : (tripleCharges (sourceA458 + difference 4 0) (sourceB458 + difference 0 4) sourceC458) = raw8261 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8261; decide +kernel
    rw [ha]
    exact (canonical8261 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA458 + difference 4 1) (sourceB458 + difference 1 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2962) := by
    have ha : (tripleCharges (sourceA458 + difference 4 1) (sourceB458 + difference 1 4) sourceC458) = raw8267 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8267; decide +kernel
    rw [ha]
    exact (canonical8267 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA458 + difference 4 2) (sourceB458 + difference 2 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2962) := by
    have ha : (tripleCharges (sourceA458 + difference 4 2) (sourceB458 + difference 2 4) sourceC458) = raw8272 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8272; decide +kernel
    rw [ha]
    exact (canonical8272 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA458 + difference 4 3) (sourceB458 + difference 3 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA458 + difference 4 3) (sourceB458 + difference 3 4) sourceC458) = raw8271 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8271; decide +kernel
    rw [ha]
    exact (canonical8271 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA458 + difference 4 4) (sourceB458 + difference 4 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA458 + difference 4 4) (sourceB458 + difference 4 4) sourceC458) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA458 + difference 4 5) (sourceB458 + difference 5 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA458 + difference 4 5) (sourceB458 + difference 5 4) sourceC458) = raw8273 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8273; decide +kernel
    rw [ha]
    exact (canonical8273 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA458 + sourceB458) sourceC458) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA458 + sourceB458) sourceC458) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA458 sourceB458 sourceC458 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA458 sourceB458 sourceC458
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm458, Integer.Sparse.eval]
  linarith only [hs]

def sourceA459 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB459 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC459 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm459 : Integer.Sparse Master := [(Sum.inr 4613, 2), (Sum.inr 4614, 1), (Sum.inr 4615, 1), (Sum.inr 4617, 1), (Sum.inr 4879, 2), (Sum.inr 4881, 1), (Sum.inr 4884, 1), (Sum.inr 4896, 1), (Sum.inr 5106, 2), (Sum.inr 5159, 2), (Sum.inr 5161, 2), (Sum.inr 5165, 2), (Sum.inr 5260, 2), (Sum.inr 5270, 2), (Sum.inr 5272, 1), (Sum.inr 5276, 1), (Sum.inr 5294, 1), (Sum.inr 5295, 2), (Sum.inr 5305, 1), (Sum.inr 5310, 1), (Sum.inr 5311, 1)]

theorem sourceEq459 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm459 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA459 + difference 0 1) (sourceB459 + difference 1 0) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA459 + difference 0 1) (sourceB459 + difference 1 0) sourceC459) = raw6372 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw6372; decide +kernel
    rw [ha]
    exact (canonical6372 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA459 + difference 0 2) (sourceB459 + difference 2 0) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA459 + difference 0 2) (sourceB459 + difference 2 0) sourceC459) = raw8274 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8274; decide +kernel
    rw [ha]
    exact (canonical8274 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA459 + difference 0 3) (sourceB459 + difference 3 0) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA459 + difference 0 3) (sourceB459 + difference 3 0) sourceC459) = raw7647 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw7647; decide +kernel
    rw [ha]
    exact (canonical7647 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA459 + difference 0 4) (sourceB459 + difference 4 0) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA459 + difference 0 4) (sourceB459 + difference 4 0) sourceC459) = raw8063 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8063; decide +kernel
    rw [ha]
    exact (canonical8063 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA459 + difference 0 5) (sourceB459 + difference 5 0) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA459 + difference 0 5) (sourceB459 + difference 5 0) sourceC459) = raw8275 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8275; decide +kernel
    rw [ha]
    exact (canonical8275 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA459 + difference 1 0) (sourceB459 + difference 0 1) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA459 + difference 1 0) (sourceB459 + difference 0 1) sourceC459) = raw8276 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8276; decide +kernel
    rw [ha]
    exact (canonical8276 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA459 + difference 1 2) (sourceB459 + difference 2 1) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5159) := by
    have ha : (tripleCharges (sourceA459 + difference 1 2) (sourceB459 + difference 2 1) sourceC459) = raw8277 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8277; decide +kernel
    rw [ha]
    exact (canonical8277 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA459 + difference 1 3) (sourceB459 + difference 3 1) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA459 + difference 1 3) (sourceB459 + difference 3 1) sourceC459) = raw7652 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw7652; decide +kernel
    rw [ha]
    exact (canonical7652 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA459 + difference 1 4) (sourceB459 + difference 4 1) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA459 + difference 1 4) (sourceB459 + difference 4 1) sourceC459) = raw8065 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8065; decide +kernel
    rw [ha]
    exact (canonical8065 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA459 + difference 1 5) (sourceB459 + difference 5 1) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4613) := by
    have ha : (tripleCharges (sourceA459 + difference 1 5) (sourceB459 + difference 5 1) sourceC459) = raw8278 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8278; decide +kernel
    rw [ha]
    exact (canonical8278 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA459 + difference 2 0) (sourceB459 + difference 0 2) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA459 + difference 2 0) (sourceB459 + difference 0 2) sourceC459) = raw8279 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8279; decide +kernel
    rw [ha]
    exact (canonical8279 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA459 + difference 2 1) (sourceB459 + difference 1 2) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5159) := by
    have ha : (tripleCharges (sourceA459 + difference 2 1) (sourceB459 + difference 1 2) sourceC459) = raw6380 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw6380; decide +kernel
    rw [ha]
    exact (canonical6380 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA459 + difference 2 3) (sourceB459 + difference 3 2) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA459 + difference 2 3) (sourceB459 + difference 3 2) sourceC459) = raw7655 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw7655; decide +kernel
    rw [ha]
    exact (canonical7655 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA459 + difference 2 4) (sourceB459 + difference 4 2) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA459 + difference 2 4) (sourceB459 + difference 4 2) sourceC459) = raw7528 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw7528; decide +kernel
    rw [ha]
    exact (canonical7528 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA459 + difference 2 5) (sourceB459 + difference 5 2) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4613) := by
    have ha : (tripleCharges (sourceA459 + difference 2 5) (sourceB459 + difference 5 2) sourceC459) = raw8280 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8280; decide +kernel
    rw [ha]
    exact (canonical8280 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA459 + difference 3 0) (sourceB459 + difference 0 3) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA459 + difference 3 0) (sourceB459 + difference 0 3) sourceC459) = raw8281 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8281; decide +kernel
    rw [ha]
    exact (canonical8281 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA459 + difference 3 1) (sourceB459 + difference 1 3) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5165) := by
    have ha : (tripleCharges (sourceA459 + difference 3 1) (sourceB459 + difference 1 3) sourceC459) = raw6385 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw6385; decide +kernel
    rw [ha]
    exact (canonical6385 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA459 + difference 3 2) (sourceB459 + difference 2 3) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5165) := by
    have ha : (tripleCharges (sourceA459 + difference 3 2) (sourceB459 + difference 2 3) sourceC459) = raw8282 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8282; decide +kernel
    rw [ha]
    exact (canonical8282 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA459 + difference 3 4) (sourceB459 + difference 4 3) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA459 + difference 3 4) (sourceB459 + difference 4 3) sourceC459) = raw7055 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw7055; decide +kernel
    rw [ha]
    exact (canonical7055 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA459 + difference 3 5) (sourceB459 + difference 5 3) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4615) := by
    have ha : (tripleCharges (sourceA459 + difference 3 5) (sourceB459 + difference 5 3) sourceC459) = raw8283 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8283; decide +kernel
    rw [ha]
    exact (canonical8283 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA459 + difference 4 0) (sourceB459 + difference 0 4) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA459 + difference 4 0) (sourceB459 + difference 0 4) sourceC459) = raw8284 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8284; decide +kernel
    rw [ha]
    exact (canonical8284 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA459 + difference 4 1) (sourceB459 + difference 1 4) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5106) := by
    have ha : (tripleCharges (sourceA459 + difference 4 1) (sourceB459 + difference 1 4) sourceC459) = raw6029 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw6029; decide +kernel
    rw [ha]
    exact (canonical6029 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA459 + difference 4 2) (sourceB459 + difference 2 4) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5106) := by
    have ha : (tripleCharges (sourceA459 + difference 4 2) (sourceB459 + difference 2 4) sourceC459) = raw8285 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8285; decide +kernel
    rw [ha]
    exact (canonical8285 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA459 + difference 4 3) (sourceB459 + difference 3 4) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5311) := by
    have ha : (tripleCharges (sourceA459 + difference 4 3) (sourceB459 + difference 3 4) sourceC459) = raw6019 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw6019; decide +kernel
    rw [ha]
    exact (canonical6019 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA459 + difference 4 5) (sourceB459 + difference 5 4) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4614) := by
    have ha : (tripleCharges (sourceA459 + difference 4 5) (sourceB459 + difference 5 4) sourceC459) = raw8286 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw8286; decide +kernel
    rw [ha]
    exact (canonical8286 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA459 + difference 5 0) (sourceB459 + difference 0 5) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA459 + difference 5 0) (sourceB459 + difference 0 5) sourceC459) = raw6373 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw6373; decide +kernel
    rw [ha]
    exact (canonical6373 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA459 + difference 5 1) (sourceB459 + difference 1 5) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA459 + difference 5 1) (sourceB459 + difference 1 5) sourceC459) = raw6028 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw6028; decide +kernel
    rw [ha]
    exact (canonical6028 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA459 + difference 5 2) (sourceB459 + difference 2 5) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA459 + difference 5 2) (sourceB459 + difference 2 5) sourceC459) = raw6374 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw6374; decide +kernel
    rw [ha]
    exact (canonical6374 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA459 + difference 5 3) (sourceB459 + difference 3 5) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA459 + difference 5 3) (sourceB459 + difference 3 5) sourceC459) = raw6018 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw6018; decide +kernel
    rw [ha]
    exact (canonical6018 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA459 + difference 5 4) (sourceB459 + difference 4 5) sourceC459) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA459 + difference 5 4) (sourceB459 + difference 4 5) sourceC459) = raw6375 := by
      apply Matrix.ext; unfold tripleCharges sourceA459 sourceB459 sourceC459 difference raw6375; decide +kernel
    rw [ha]
    exact (canonical6375 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA459 sourceB459 sourceC459
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm459, Integer.Sparse.eval]
  linarith only [hs]

def sourceA460 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB460 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC460 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm460 : Integer.Sparse Master := [(Sum.inr 1286, 2), (Sum.inr 1287, 1), (Sum.inr 1288, 1), (Sum.inr 1306, 1), (Sum.inr 2246, 2), (Sum.inr 2266, 1), (Sum.inr 2267, 1), (Sum.inr 2280, 1), (Sum.inr 2711, 2), (Sum.inr 2724, 2), (Sum.inr 2725, 2), (Sum.inr 2733, 2), (Sum.inr 2754, 2), (Sum.inr 2768, 1), (Sum.inr 2769, 2), (Sum.inr 2777, 1), (Sum.inr 2788, 1), (Sum.inr 2789, 1), (Sum.inr 2964, 2), (Sum.inr 3113, 1), (Sum.inr 3125, 1)]

theorem sourceEq460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm460 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA460 + difference 0 1) (sourceB460 + difference 1 0) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA460 + difference 0 1) (sourceB460 + difference 1 0) sourceC460) = raw6394 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw6394; decide +kernel
    rw [ha]
    exact (canonical6394 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA460 + difference 0 2) (sourceB460 + difference 2 0) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA460 + difference 0 2) (sourceB460 + difference 2 0) sourceC460) = raw8287 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8287; decide +kernel
    rw [ha]
    exact (canonical8287 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA460 + difference 0 3) (sourceB460 + difference 3 0) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3125) := by
    have ha : (tripleCharges (sourceA460 + difference 0 3) (sourceB460 + difference 3 0) sourceC460) = raw7663 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw7663; decide +kernel
    rw [ha]
    exact (canonical7663 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA460 + difference 0 4) (sourceB460 + difference 4 0) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA460 + difference 0 4) (sourceB460 + difference 4 0) sourceC460) = raw8067 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8067; decide +kernel
    rw [ha]
    exact (canonical8067 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA460 + difference 0 5) (sourceB460 + difference 5 0) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA460 + difference 0 5) (sourceB460 + difference 5 0) sourceC460) = raw8288 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8288; decide +kernel
    rw [ha]
    exact (canonical8288 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA460 + difference 1 0) (sourceB460 + difference 0 1) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA460 + difference 1 0) (sourceB460 + difference 0 1) sourceC460) = raw8289 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8289; decide +kernel
    rw [ha]
    exact (canonical8289 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA460 + difference 1 2) (sourceB460 + difference 2 1) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2711) := by
    have ha : (tripleCharges (sourceA460 + difference 1 2) (sourceB460 + difference 2 1) sourceC460) = raw8290 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8290; decide +kernel
    rw [ha]
    exact (canonical8290 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA460 + difference 1 3) (sourceB460 + difference 3 1) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA460 + difference 1 3) (sourceB460 + difference 3 1) sourceC460) = raw7668 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw7668; decide +kernel
    rw [ha]
    exact (canonical7668 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA460 + difference 1 4) (sourceB460 + difference 4 1) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA460 + difference 1 4) (sourceB460 + difference 4 1) sourceC460) = raw8069 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8069; decide +kernel
    rw [ha]
    exact (canonical8069 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA460 + difference 1 5) (sourceB460 + difference 5 1) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA460 + difference 1 5) (sourceB460 + difference 5 1) sourceC460) = raw8291 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8291; decide +kernel
    rw [ha]
    exact (canonical8291 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA460 + difference 2 0) (sourceB460 + difference 0 2) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA460 + difference 2 0) (sourceB460 + difference 0 2) sourceC460) = raw8292 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8292; decide +kernel
    rw [ha]
    exact (canonical8292 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA460 + difference 2 1) (sourceB460 + difference 1 2) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2711) := by
    have ha : (tripleCharges (sourceA460 + difference 2 1) (sourceB460 + difference 1 2) sourceC460) = raw6402 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw6402; decide +kernel
    rw [ha]
    exact (canonical6402 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA460 + difference 2 3) (sourceB460 + difference 3 2) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA460 + difference 2 3) (sourceB460 + difference 3 2) sourceC460) = raw7671 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw7671; decide +kernel
    rw [ha]
    exact (canonical7671 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA460 + difference 2 4) (sourceB460 + difference 4 2) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA460 + difference 2 4) (sourceB460 + difference 4 2) sourceC460) = raw7537 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw7537; decide +kernel
    rw [ha]
    exact (canonical7537 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA460 + difference 2 5) (sourceB460 + difference 5 2) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA460 + difference 2 5) (sourceB460 + difference 5 2) sourceC460) = raw8293 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8293; decide +kernel
    rw [ha]
    exact (canonical8293 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA460 + difference 3 0) (sourceB460 + difference 0 3) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA460 + difference 3 0) (sourceB460 + difference 0 3) sourceC460) = raw8294 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8294; decide +kernel
    rw [ha]
    exact (canonical8294 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA460 + difference 3 1) (sourceB460 + difference 1 3) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2733) := by
    have ha : (tripleCharges (sourceA460 + difference 3 1) (sourceB460 + difference 1 3) sourceC460) = raw6407 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw6407; decide +kernel
    rw [ha]
    exact (canonical6407 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA460 + difference 3 2) (sourceB460 + difference 2 3) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2733) := by
    have ha : (tripleCharges (sourceA460 + difference 3 2) (sourceB460 + difference 2 3) sourceC460) = raw8295 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8295; decide +kernel
    rw [ha]
    exact (canonical8295 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA460 + difference 3 4) (sourceB460 + difference 4 3) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA460 + difference 3 4) (sourceB460 + difference 4 3) sourceC460) = raw7069 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw7069; decide +kernel
    rw [ha]
    exact (canonical7069 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA460 + difference 3 5) (sourceB460 + difference 5 3) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1288) := by
    have ha : (tripleCharges (sourceA460 + difference 3 5) (sourceB460 + difference 5 3) sourceC460) = raw8296 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8296; decide +kernel
    rw [ha]
    exact (canonical8296 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA460 + difference 4 0) (sourceB460 + difference 0 4) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA460 + difference 4 0) (sourceB460 + difference 0 4) sourceC460) = raw8297 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8297; decide +kernel
    rw [ha]
    exact (canonical8297 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA460 + difference 4 1) (sourceB460 + difference 1 4) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2725) := by
    have ha : (tripleCharges (sourceA460 + difference 4 1) (sourceB460 + difference 1 4) sourceC460) = raw6059 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw6059; decide +kernel
    rw [ha]
    exact (canonical6059 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA460 + difference 4 2) (sourceB460 + difference 2 4) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2725) := by
    have ha : (tripleCharges (sourceA460 + difference 4 2) (sourceB460 + difference 2 4) sourceC460) = raw8298 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8298; decide +kernel
    rw [ha]
    exact (canonical8298 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA460 + difference 4 3) (sourceB460 + difference 3 4) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA460 + difference 4 3) (sourceB460 + difference 3 4) sourceC460) = raw6049 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw6049; decide +kernel
    rw [ha]
    exact (canonical6049 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA460 + difference 4 5) (sourceB460 + difference 5 4) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1287) := by
    have ha : (tripleCharges (sourceA460 + difference 4 5) (sourceB460 + difference 5 4) sourceC460) = raw8299 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw8299; decide +kernel
    rw [ha]
    exact (canonical8299 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA460 + difference 5 0) (sourceB460 + difference 0 5) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA460 + difference 5 0) (sourceB460 + difference 0 5) sourceC460) = raw6395 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw6395; decide +kernel
    rw [ha]
    exact (canonical6395 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA460 + difference 5 1) (sourceB460 + difference 1 5) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA460 + difference 5 1) (sourceB460 + difference 1 5) sourceC460) = raw6058 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw6058; decide +kernel
    rw [ha]
    exact (canonical6058 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA460 + difference 5 2) (sourceB460 + difference 2 5) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA460 + difference 5 2) (sourceB460 + difference 2 5) sourceC460) = raw6396 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw6396; decide +kernel
    rw [ha]
    exact (canonical6396 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA460 + difference 5 3) (sourceB460 + difference 3 5) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA460 + difference 5 3) (sourceB460 + difference 3 5) sourceC460) = raw6048 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw6048; decide +kernel
    rw [ha]
    exact (canonical6048 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA460 + difference 5 4) (sourceB460 + difference 4 5) sourceC460) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA460 + difference 5 4) (sourceB460 + difference 4 5) sourceC460) = raw6397 := by
      apply Matrix.ext; unfold tripleCharges sourceA460 sourceB460 sourceC460 difference raw6397; decide +kernel
    rw [ha]
    exact (canonical6397 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA460 sourceB460 sourceC460
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm460, Integer.Sparse.eval]
  linarith only [hs]

def sourceA461 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB461 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC461 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm461 : Integer.Sparse Master := [(Sum.inr 2516, 2), (Sum.inr 2520, 1), (Sum.inr 2521, 1), (Sum.inr 2719, 2), (Sum.inr 2737, 1), (Sum.inr 2740, 1), (Sum.inr 2783, 1), (Sum.inr 2789, 1), (Sum.inr 3035, 2), (Sum.inr 3049, 1), (Sum.inr 3052, 1), (Sum.inr 3063, 2), (Sum.inr 3072, 2), (Sum.inr 3075, 2), (Sum.inr 3086, 2), (Sum.inr 3098, 2), (Sum.inr 3101, 1), (Sum.inr 3121, 1), (Sum.inr 3158, 2), (Sum.inr 3161, 1), (Sum.inr 3225, 1)]

theorem sourceEq461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm461 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA461 + difference 0 1) (sourceB461 + difference 1 0) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA461 + difference 0 1) (sourceB461 + difference 1 0) sourceC461) = raw6416 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw6416; decide +kernel
    rw [ha]
    exact (canonical6416 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA461 + difference 0 2) (sourceB461 + difference 2 0) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA461 + difference 0 2) (sourceB461 + difference 2 0) sourceC461) = raw8300 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8300; decide +kernel
    rw [ha]
    exact (canonical8300 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA461 + difference 0 3) (sourceB461 + difference 3 0) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA461 + difference 0 3) (sourceB461 + difference 3 0) sourceC461) = raw7679 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw7679; decide +kernel
    rw [ha]
    exact (canonical7679 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA461 + difference 0 4) (sourceB461 + difference 4 0) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA461 + difference 0 4) (sourceB461 + difference 4 0) sourceC461) = raw8301 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8301; decide +kernel
    rw [ha]
    exact (canonical8301 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA461 + difference 0 5) (sourceB461 + difference 5 0) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA461 + difference 0 5) (sourceB461 + difference 5 0) sourceC461) = raw8302 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8302; decide +kernel
    rw [ha]
    exact (canonical8302 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA461 + difference 1 0) (sourceB461 + difference 0 1) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA461 + difference 1 0) (sourceB461 + difference 0 1) sourceC461) = raw8303 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8303; decide +kernel
    rw [ha]
    exact (canonical8303 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA461 + difference 1 2) (sourceB461 + difference 2 1) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3063) := by
    have ha : (tripleCharges (sourceA461 + difference 1 2) (sourceB461 + difference 2 1) sourceC461) = raw8304 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8304; decide +kernel
    rw [ha]
    exact (canonical8304 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA461 + difference 1 3) (sourceB461 + difference 3 1) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA461 + difference 1 3) (sourceB461 + difference 3 1) sourceC461) = raw7684 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw7684; decide +kernel
    rw [ha]
    exact (canonical7684 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA461 + difference 1 4) (sourceB461 + difference 4 1) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA461 + difference 1 4) (sourceB461 + difference 4 1) sourceC461) = raw8305 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8305; decide +kernel
    rw [ha]
    exact (canonical8305 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA461 + difference 1 5) (sourceB461 + difference 5 1) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3072) := by
    have ha : (tripleCharges (sourceA461 + difference 1 5) (sourceB461 + difference 5 1) sourceC461) = raw8306 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8306; decide +kernel
    rw [ha]
    exact (canonical8306 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA461 + difference 2 0) (sourceB461 + difference 0 2) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA461 + difference 2 0) (sourceB461 + difference 0 2) sourceC461) = raw8307 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8307; decide +kernel
    rw [ha]
    exact (canonical8307 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA461 + difference 2 1) (sourceB461 + difference 1 2) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3063) := by
    have ha : (tripleCharges (sourceA461 + difference 2 1) (sourceB461 + difference 1 2) sourceC461) = raw6424 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw6424; decide +kernel
    rw [ha]
    exact (canonical6424 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA461 + difference 2 3) (sourceB461 + difference 3 2) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA461 + difference 2 3) (sourceB461 + difference 3 2) sourceC461) = raw7687 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw7687; decide +kernel
    rw [ha]
    exact (canonical7687 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA461 + difference 2 4) (sourceB461 + difference 4 2) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA461 + difference 2 4) (sourceB461 + difference 4 2) sourceC461) = raw7546 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw7546; decide +kernel
    rw [ha]
    exact (canonical7546 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA461 + difference 2 5) (sourceB461 + difference 5 2) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3072) := by
    have ha : (tripleCharges (sourceA461 + difference 2 5) (sourceB461 + difference 5 2) sourceC461) = raw8308 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8308; decide +kernel
    rw [ha]
    exact (canonical8308 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA461 + difference 3 0) (sourceB461 + difference 0 3) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA461 + difference 3 0) (sourceB461 + difference 0 3) sourceC461) = raw8309 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8309; decide +kernel
    rw [ha]
    exact (canonical8309 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA461 + difference 3 1) (sourceB461 + difference 1 3) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3035) := by
    have ha : (tripleCharges (sourceA461 + difference 3 1) (sourceB461 + difference 1 3) sourceC461) = raw6429 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw6429; decide +kernel
    rw [ha]
    exact (canonical6429 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA461 + difference 3 2) (sourceB461 + difference 2 3) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3035) := by
    have ha : (tripleCharges (sourceA461 + difference 3 2) (sourceB461 + difference 2 3) sourceC461) = raw8310 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8310; decide +kernel
    rw [ha]
    exact (canonical8310 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA461 + difference 3 4) (sourceB461 + difference 4 3) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA461 + difference 3 4) (sourceB461 + difference 4 3) sourceC461) = raw7083 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw7083; decide +kernel
    rw [ha]
    exact (canonical7083 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA461 + difference 3 5) (sourceB461 + difference 5 3) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3049) := by
    have ha : (tripleCharges (sourceA461 + difference 3 5) (sourceB461 + difference 5 3) sourceC461) = raw8311 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8311; decide +kernel
    rw [ha]
    exact (canonical8311 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA461 + difference 4 0) (sourceB461 + difference 0 4) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA461 + difference 4 0) (sourceB461 + difference 0 4) sourceC461) = raw8312 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8312; decide +kernel
    rw [ha]
    exact (canonical8312 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA461 + difference 4 1) (sourceB461 + difference 1 4) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA461 + difference 4 1) (sourceB461 + difference 1 4) sourceC461) = raw6089 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw6089; decide +kernel
    rw [ha]
    exact (canonical6089 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA461 + difference 4 2) (sourceB461 + difference 2 4) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA461 + difference 4 2) (sourceB461 + difference 2 4) sourceC461) = raw8313 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8313; decide +kernel
    rw [ha]
    exact (canonical8313 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA461 + difference 4 3) (sourceB461 + difference 3 4) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA461 + difference 4 3) (sourceB461 + difference 3 4) sourceC461) = raw6079 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw6079; decide +kernel
    rw [ha]
    exact (canonical6079 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA461 + difference 4 5) (sourceB461 + difference 5 4) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2521) := by
    have ha : (tripleCharges (sourceA461 + difference 4 5) (sourceB461 + difference 5 4) sourceC461) = raw8314 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw8314; decide +kernel
    rw [ha]
    exact (canonical8314 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA461 + difference 5 0) (sourceB461 + difference 0 5) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA461 + difference 5 0) (sourceB461 + difference 0 5) sourceC461) = raw6417 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw6417; decide +kernel
    rw [ha]
    exact (canonical6417 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA461 + difference 5 1) (sourceB461 + difference 1 5) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA461 + difference 5 1) (sourceB461 + difference 1 5) sourceC461) = raw6088 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw6088; decide +kernel
    rw [ha]
    exact (canonical6088 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA461 + difference 5 2) (sourceB461 + difference 2 5) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA461 + difference 5 2) (sourceB461 + difference 2 5) sourceC461) = raw6418 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw6418; decide +kernel
    rw [ha]
    exact (canonical6418 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA461 + difference 5 3) (sourceB461 + difference 3 5) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA461 + difference 5 3) (sourceB461 + difference 3 5) sourceC461) = raw6078 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw6078; decide +kernel
    rw [ha]
    exact (canonical6078 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA461 + difference 5 4) (sourceB461 + difference 4 5) sourceC461) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA461 + difference 5 4) (sourceB461 + difference 4 5) sourceC461) = raw6419 := by
      apply Matrix.ext; unfold tripleCharges sourceA461 sourceB461 sourceC461 difference raw6419; decide +kernel
    rw [ha]
    exact (canonical6419 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA461 sourceB461 sourceC461
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm461, Integer.Sparse.eval]
  linarith only [hs]

def sourceA462 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB462 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC462 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm462 : Integer.Sparse Master := [(Sum.inr 1292, 1), (Sum.inr 2588, 2), (Sum.inr 2740, 1), (Sum.inr 2781, 1), (Sum.inr 2783, 1), (Sum.inr 4084, -1)]

theorem sourceEq462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm462 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA462 + difference 0 0) (sourceB462 + difference 0 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA462 + difference 0 0) (sourceB462 + difference 0 0) sourceC462) = raw6446 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw6446; decide +kernel
    rw [ha]
    exact (canonical6446 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA462 + difference 0 1) (sourceB462 + difference 1 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2588) := by
    have ha : (tripleCharges (sourceA462 + difference 0 1) (sourceB462 + difference 1 0) sourceC462) = raw6438 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw6438; decide +kernel
    rw [ha]
    exact (canonical6438 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA462 + difference 0 2) (sourceB462 + difference 2 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2588) := by
    have ha : (tripleCharges (sourceA462 + difference 0 2) (sourceB462 + difference 2 0) sourceC462) = raw8315 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw8315; decide +kernel
    rw [ha]
    exact (canonical8315 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA462 + difference 0 3) (sourceB462 + difference 3 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA462 + difference 0 3) (sourceB462 + difference 3 0) sourceC462) = raw7695 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw7695; decide +kernel
    rw [ha]
    exact (canonical7695 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA462 + difference 0 4) (sourceB462 + difference 4 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA462 + difference 0 4) (sourceB462 + difference 4 0) sourceC462) = raw8316 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw8316; decide +kernel
    rw [ha]
    exact (canonical8316 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA462 + difference 0 5) (sourceB462 + difference 5 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1292) := by
    have ha : (tripleCharges (sourceA462 + difference 0 5) (sourceB462 + difference 5 0) sourceC462) = raw8317 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw8317; decide +kernel
    rw [ha]
    exact (canonical8317 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA462 + sourceB462) sourceC462) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA462 + sourceB462) sourceC462) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA462 sourceB462 sourceC462 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA462 sourceB462 sourceC462
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm462, Integer.Sparse.eval]
  linarith only [hs]

def sourceA463 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB463 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC463 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm463 : Integer.Sparse Master := [(Sum.inr 2132, 2), (Sum.inr 2134, 1), (Sum.inr 2138, 1), (Sum.inr 2278, 1), (Sum.inr 2781, 1), (Sum.inr 4084, -1)]

theorem sourceEq463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm463 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA463 + difference 0 0) (sourceB463 + difference 0 0) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA463 + difference 0 0) (sourceB463 + difference 0 0) sourceC463) = raw6446 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw6446; decide +kernel
    rw [ha]
    exact (canonical6446 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA463 + difference 1 0) (sourceB463 + difference 0 1) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2132) := by
    have ha : (tripleCharges (sourceA463 + difference 1 0) (sourceB463 + difference 0 1) sourceC463) = raw8318 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw8318; decide +kernel
    rw [ha]
    exact (canonical8318 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA463 + difference 2 0) (sourceB463 + difference 0 2) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2132) := by
    have ha : (tripleCharges (sourceA463 + difference 2 0) (sourceB463 + difference 0 2) sourceC463) = raw8319 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw8319; decide +kernel
    rw [ha]
    exact (canonical8319 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA463 + difference 3 0) (sourceB463 + difference 0 3) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA463 + difference 3 0) (sourceB463 + difference 0 3) sourceC463) = raw8320 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw8320; decide +kernel
    rw [ha]
    exact (canonical8320 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA463 + difference 4 0) (sourceB463 + difference 0 4) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA463 + difference 4 0) (sourceB463 + difference 0 4) sourceC463) = raw8321 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw8321; decide +kernel
    rw [ha]
    exact (canonical8321 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA463 + difference 5 0) (sourceB463 + difference 0 5) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA463 + difference 5 0) (sourceB463 + difference 0 5) sourceC463) = raw6439 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw6439; decide +kernel
    rw [ha]
    exact (canonical6439 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA463 + sourceB463) sourceC463) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA463 + sourceB463) sourceC463) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA463 sourceB463 sourceC463 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA463 sourceB463 sourceC463
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm463, Integer.Sparse.eval]
  linarith only [hs]

def sourceA464 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB464 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC464 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm464 : Integer.Sparse Master := [(Sum.inr 1290, 1), (Sum.inr 2132, 1), (Sum.inr 2586, 1), (Sum.inr 2738, 1), (Sum.inr 2781, 2), (Sum.inr 4084, -1)]

theorem sourceEq464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm464 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA464 + difference 1 0) (sourceB464 + difference 0 1) sourceC464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2132) := by
    have ha : (tripleCharges (sourceA464 + difference 1 0) (sourceB464 + difference 0 1) sourceC464) = raw8318 := by
      apply Matrix.ext; unfold tripleCharges sourceA464 sourceB464 sourceC464 difference raw8318; decide +kernel
    rw [ha]
    exact (canonical8318 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA464 + difference 1 1) (sourceB464 + difference 1 1) sourceC464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA464 + difference 1 1) (sourceB464 + difference 1 1) sourceC464) = raw6446 := by
      apply Matrix.ext; unfold tripleCharges sourceA464 sourceB464 sourceC464 difference raw6446; decide +kernel
    rw [ha]
    exact (canonical6446 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA464 + difference 1 2) (sourceB464 + difference 2 1) sourceC464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2586) := by
    have ha : (tripleCharges (sourceA464 + difference 1 2) (sourceB464 + difference 2 1) sourceC464) = raw8322 := by
      apply Matrix.ext; unfold tripleCharges sourceA464 sourceB464 sourceC464 difference raw8322; decide +kernel
    rw [ha]
    exact (canonical8322 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA464 + difference 1 3) (sourceB464 + difference 3 1) sourceC464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA464 + difference 1 3) (sourceB464 + difference 3 1) sourceC464) = raw8323 := by
      apply Matrix.ext; unfold tripleCharges sourceA464 sourceB464 sourceC464 difference raw8323; decide +kernel
    rw [ha]
    exact (canonical8323 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA464 + difference 1 4) (sourceB464 + difference 4 1) sourceC464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA464 + difference 1 4) (sourceB464 + difference 4 1) sourceC464) = raw8324 := by
      apply Matrix.ext; unfold tripleCharges sourceA464 sourceB464 sourceC464 difference raw8324; decide +kernel
    rw [ha]
    exact (canonical8324 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA464 + difference 1 5) (sourceB464 + difference 5 1) sourceC464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1290) := by
    have ha : (tripleCharges (sourceA464 + difference 1 5) (sourceB464 + difference 5 1) sourceC464) = raw8325 := by
      apply Matrix.ext; unfold tripleCharges sourceA464 sourceB464 sourceC464 difference raw8325; decide +kernel
    rw [ha]
    exact (canonical8325 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA464 + sourceB464) sourceC464) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA464 + sourceB464) sourceC464) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA464 sourceB464 sourceC464 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA464 sourceB464 sourceC464
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm464, Integer.Sparse.eval]
  linarith only [hs]

def sourceA465 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB465 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC465 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceForm465 : Integer.Sparse Master := [(Sum.inr 4571, 2), (Sum.inr 4573, 1), (Sum.inr 4574, 1), (Sum.inr 4620, 1), (Sum.inr 5008, 2), (Sum.inr 5019, 2), (Sum.inr 5022, 2), (Sum.inr 5153, 2), (Sum.inr 5164, 2), (Sum.inr 5211, 2), (Sum.inr 5266, 2), (Sum.inr 5268, 1), (Sum.inr 5275, 1), (Sum.inr 5276, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 1), (Sum.inr 5304, 1), (Sum.inr 5436, 2), (Sum.inr 5443, 2)]

theorem sourceEq465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm465 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA465 + difference 0 1) (sourceB465 + difference 1 0) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA465 + difference 0 1) (sourceB465 + difference 1 0) sourceC465) = raw8326 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8326; decide +kernel
    rw [ha]
    exact (canonical8326 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA465 + difference 0 2) (sourceB465 + difference 2 0) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA465 + difference 0 2) (sourceB465 + difference 2 0) sourceC465) = raw8327 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8327; decide +kernel
    rw [ha]
    exact (canonical8327 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA465 + difference 0 3) (sourceB465 + difference 3 0) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA465 + difference 0 3) (sourceB465 + difference 3 0) sourceC465) = raw8328 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8328; decide +kernel
    rw [ha]
    exact (canonical8328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA465 + difference 0 4) (sourceB465 + difference 4 0) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA465 + difference 0 4) (sourceB465 + difference 4 0) sourceC465) = raw8329 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8329; decide +kernel
    rw [ha]
    exact (canonical8329 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA465 + difference 0 5) (sourceB465 + difference 5 0) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA465 + difference 0 5) (sourceB465 + difference 5 0) sourceC465) = raw8330 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8330; decide +kernel
    rw [ha]
    exact (canonical8330 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA465 + difference 1 0) (sourceB465 + difference 0 1) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4571) := by
    have ha : (tripleCharges (sourceA465 + difference 1 0) (sourceB465 + difference 0 1) sourceC465) = raw8331 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8331; decide +kernel
    rw [ha]
    exact (canonical8331 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA465 + difference 1 2) (sourceB465 + difference 2 1) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5153) := by
    have ha : (tripleCharges (sourceA465 + difference 1 2) (sourceB465 + difference 2 1) sourceC465) = raw8332 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8332; decide +kernel
    rw [ha]
    exact (canonical8332 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA465 + difference 1 3) (sourceB465 + difference 3 1) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5211) := by
    have ha : (tripleCharges (sourceA465 + difference 1 3) (sourceB465 + difference 3 1) sourceC465) = raw8333 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8333; decide +kernel
    rw [ha]
    exact (canonical8333 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA465 + difference 1 4) (sourceB465 + difference 4 1) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA465 + difference 1 4) (sourceB465 + difference 4 1) sourceC465) = raw8334 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8334; decide +kernel
    rw [ha]
    exact (canonical8334 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA465 + difference 1 5) (sourceB465 + difference 5 1) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA465 + difference 1 5) (sourceB465 + difference 5 1) sourceC465) = raw8335 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8335; decide +kernel
    rw [ha]
    exact (canonical8335 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA465 + difference 2 0) (sourceB465 + difference 0 2) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4571) := by
    have ha : (tripleCharges (sourceA465 + difference 2 0) (sourceB465 + difference 0 2) sourceC465) = raw8336 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8336; decide +kernel
    rw [ha]
    exact (canonical8336 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA465 + difference 2 1) (sourceB465 + difference 1 2) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5153) := by
    have ha : (tripleCharges (sourceA465 + difference 2 1) (sourceB465 + difference 1 2) sourceC465) = raw8337 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8337; decide +kernel
    rw [ha]
    exact (canonical8337 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA465 + difference 2 3) (sourceB465 + difference 3 2) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5211) := by
    have ha : (tripleCharges (sourceA465 + difference 2 3) (sourceB465 + difference 3 2) sourceC465) = raw8338 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8338; decide +kernel
    rw [ha]
    exact (canonical8338 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA465 + difference 2 4) (sourceB465 + difference 4 2) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA465 + difference 2 4) (sourceB465 + difference 4 2) sourceC465) = raw8339 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8339; decide +kernel
    rw [ha]
    exact (canonical8339 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA465 + difference 2 5) (sourceB465 + difference 5 2) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA465 + difference 2 5) (sourceB465 + difference 5 2) sourceC465) = raw8340 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8340; decide +kernel
    rw [ha]
    exact (canonical8340 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA465 + difference 3 0) (sourceB465 + difference 0 3) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4620) := by
    have ha : (tripleCharges (sourceA465 + difference 3 0) (sourceB465 + difference 0 3) sourceC465) = raw8341 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8341; decide +kernel
    rw [ha]
    exact (canonical8341 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA465 + difference 3 1) (sourceB465 + difference 1 3) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA465 + difference 3 1) (sourceB465 + difference 1 3) sourceC465) = raw8342 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8342; decide +kernel
    rw [ha]
    exact (canonical8342 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA465 + difference 3 2) (sourceB465 + difference 2 3) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA465 + difference 3 2) (sourceB465 + difference 2 3) sourceC465) = raw8343 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8343; decide +kernel
    rw [ha]
    exact (canonical8343 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA465 + difference 3 4) (sourceB465 + difference 4 3) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA465 + difference 3 4) (sourceB465 + difference 4 3) sourceC465) = raw8344 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8344; decide +kernel
    rw [ha]
    exact (canonical8344 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA465 + difference 3 5) (sourceB465 + difference 5 3) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA465 + difference 3 5) (sourceB465 + difference 5 3) sourceC465) = raw8345 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8345; decide +kernel
    rw [ha]
    exact (canonical8345 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA465 + difference 4 0) (sourceB465 + difference 0 4) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4574) := by
    have ha : (tripleCharges (sourceA465 + difference 4 0) (sourceB465 + difference 0 4) sourceC465) = raw8346 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8346; decide +kernel
    rw [ha]
    exact (canonical8346 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA465 + difference 4 1) (sourceB465 + difference 1 4) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5019) := by
    have ha : (tripleCharges (sourceA465 + difference 4 1) (sourceB465 + difference 1 4) sourceC465) = raw8347 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8347; decide +kernel
    rw [ha]
    exact (canonical8347 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA465 + difference 4 2) (sourceB465 + difference 2 4) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5019) := by
    have ha : (tripleCharges (sourceA465 + difference 4 2) (sourceB465 + difference 2 4) sourceC465) = raw8348 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8348; decide +kernel
    rw [ha]
    exact (canonical8348 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA465 + difference 4 3) (sourceB465 + difference 3 4) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5022) := by
    have ha : (tripleCharges (sourceA465 + difference 4 3) (sourceB465 + difference 3 4) sourceC465) = raw8349 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8349; decide +kernel
    rw [ha]
    exact (canonical8349 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA465 + difference 4 5) (sourceB465 + difference 5 4) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA465 + difference 4 5) (sourceB465 + difference 5 4) sourceC465) = raw8350 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8350; decide +kernel
    rw [ha]
    exact (canonical8350 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA465 + difference 5 0) (sourceB465 + difference 0 5) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4573) := by
    have ha : (tripleCharges (sourceA465 + difference 5 0) (sourceB465 + difference 0 5) sourceC465) = raw8351 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8351; decide +kernel
    rw [ha]
    exact (canonical8351 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA465 + difference 5 1) (sourceB465 + difference 1 5) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5008) := by
    have ha : (tripleCharges (sourceA465 + difference 5 1) (sourceB465 + difference 1 5) sourceC465) = raw8352 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8352; decide +kernel
    rw [ha]
    exact (canonical8352 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA465 + difference 5 2) (sourceB465 + difference 2 5) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5008) := by
    have ha : (tripleCharges (sourceA465 + difference 5 2) (sourceB465 + difference 2 5) sourceC465) = raw8353 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8353; decide +kernel
    rw [ha]
    exact (canonical8353 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA465 + difference 5 3) (sourceB465 + difference 3 5) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5022) := by
    have ha : (tripleCharges (sourceA465 + difference 5 3) (sourceB465 + difference 3 5) sourceC465) = raw8354 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8354; decide +kernel
    rw [ha]
    exact (canonical8354 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA465 + difference 5 4) (sourceB465 + difference 4 5) sourceC465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA465 + difference 5 4) (sourceB465 + difference 4 5) sourceC465) = raw8355 := by
      apply Matrix.ext; unfold tripleCharges sourceA465 sourceB465 sourceC465 difference raw8355; decide +kernel
    rw [ha]
    exact (canonical8355 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA465 sourceB465 sourceC465
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm465, Integer.Sparse.eval]
  linarith only [hs]

def sourceA466 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB466 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC466 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceForm466 : Integer.Sparse Master := [(Sum.inr 1189, 2), (Sum.inr 1191, 1), (Sum.inr 1192, 1), (Sum.inr 1295, 1), (Sum.inr 2393, 2), (Sum.inr 2408, 1), (Sum.inr 2734, 1), (Sum.inr 2841, 2), (Sum.inr 2842, 1), (Sum.inr 2909, 2), (Sum.inr 2910, 2), (Sum.inr 2955, 2), (Sum.inr 3039, 2), (Sum.inr 3051, 2), (Sum.inr 3052, 1), (Sum.inr 3110, 1), (Sum.inr 3119, 1), (Sum.inr 3584, 1), (Sum.inr 3862, 1), (Sum.inr 3877, 2), (Sum.inr 3889, 1)]

theorem sourceEq466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm466 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA466 + difference 0 1) (sourceB466 + difference 1 0) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA466 + difference 0 1) (sourceB466 + difference 1 0) sourceC466) = raw8356 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8356; decide +kernel
    rw [ha]
    exact (canonical8356 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA466 + difference 0 2) (sourceB466 + difference 2 0) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA466 + difference 0 2) (sourceB466 + difference 2 0) sourceC466) = raw8357 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8357; decide +kernel
    rw [ha]
    exact (canonical8357 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA466 + difference 0 3) (sourceB466 + difference 3 0) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA466 + difference 0 3) (sourceB466 + difference 3 0) sourceC466) = raw8358 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8358; decide +kernel
    rw [ha]
    exact (canonical8358 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA466 + difference 0 4) (sourceB466 + difference 4 0) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA466 + difference 0 4) (sourceB466 + difference 4 0) sourceC466) = raw8359 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8359; decide +kernel
    rw [ha]
    exact (canonical8359 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA466 + difference 0 5) (sourceB466 + difference 5 0) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA466 + difference 0 5) (sourceB466 + difference 5 0) sourceC466) = raw8360 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8360; decide +kernel
    rw [ha]
    exact (canonical8360 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA466 + difference 1 0) (sourceB466 + difference 0 1) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1189) := by
    have ha : (tripleCharges (sourceA466 + difference 1 0) (sourceB466 + difference 0 1) sourceC466) = raw8361 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8361; decide +kernel
    rw [ha]
    exact (canonical8361 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA466 + difference 1 2) (sourceB466 + difference 2 1) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2909) := by
    have ha : (tripleCharges (sourceA466 + difference 1 2) (sourceB466 + difference 2 1) sourceC466) = raw8362 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8362; decide +kernel
    rw [ha]
    exact (canonical8362 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA466 + difference 1 3) (sourceB466 + difference 3 1) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2841) := by
    have ha : (tripleCharges (sourceA466 + difference 1 3) (sourceB466 + difference 3 1) sourceC466) = raw8363 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8363; decide +kernel
    rw [ha]
    exact (canonical8363 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA466 + difference 1 4) (sourceB466 + difference 4 1) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA466 + difference 1 4) (sourceB466 + difference 4 1) sourceC466) = raw8364 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8364; decide +kernel
    rw [ha]
    exact (canonical8364 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA466 + difference 1 5) (sourceB466 + difference 5 1) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA466 + difference 1 5) (sourceB466 + difference 5 1) sourceC466) = raw8365 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8365; decide +kernel
    rw [ha]
    exact (canonical8365 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA466 + difference 2 0) (sourceB466 + difference 0 2) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1189) := by
    have ha : (tripleCharges (sourceA466 + difference 2 0) (sourceB466 + difference 0 2) sourceC466) = raw8366 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8366; decide +kernel
    rw [ha]
    exact (canonical8366 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA466 + difference 2 1) (sourceB466 + difference 1 2) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2909) := by
    have ha : (tripleCharges (sourceA466 + difference 2 1) (sourceB466 + difference 1 2) sourceC466) = raw8367 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8367; decide +kernel
    rw [ha]
    exact (canonical8367 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA466 + difference 2 3) (sourceB466 + difference 3 2) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2841) := by
    have ha : (tripleCharges (sourceA466 + difference 2 3) (sourceB466 + difference 3 2) sourceC466) = raw8368 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8368; decide +kernel
    rw [ha]
    exact (canonical8368 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA466 + difference 2 4) (sourceB466 + difference 4 2) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA466 + difference 2 4) (sourceB466 + difference 4 2) sourceC466) = raw8369 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8369; decide +kernel
    rw [ha]
    exact (canonical8369 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA466 + difference 2 5) (sourceB466 + difference 5 2) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA466 + difference 2 5) (sourceB466 + difference 5 2) sourceC466) = raw8370 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8370; decide +kernel
    rw [ha]
    exact (canonical8370 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA466 + difference 3 0) (sourceB466 + difference 0 3) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1295) := by
    have ha : (tripleCharges (sourceA466 + difference 3 0) (sourceB466 + difference 0 3) sourceC466) = raw8371 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8371; decide +kernel
    rw [ha]
    exact (canonical8371 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA466 + difference 3 1) (sourceB466 + difference 1 3) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA466 + difference 3 1) (sourceB466 + difference 1 3) sourceC466) = raw8372 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8372; decide +kernel
    rw [ha]
    exact (canonical8372 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA466 + difference 3 2) (sourceB466 + difference 2 3) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA466 + difference 3 2) (sourceB466 + difference 2 3) sourceC466) = raw8373 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8373; decide +kernel
    rw [ha]
    exact (canonical8373 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA466 + difference 3 4) (sourceB466 + difference 4 3) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA466 + difference 3 4) (sourceB466 + difference 4 3) sourceC466) = raw8374 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8374; decide +kernel
    rw [ha]
    exact (canonical8374 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA466 + difference 3 5) (sourceB466 + difference 5 3) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA466 + difference 3 5) (sourceB466 + difference 5 3) sourceC466) = raw8375 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8375; decide +kernel
    rw [ha]
    exact (canonical8375 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA466 + difference 4 0) (sourceB466 + difference 0 4) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1192) := by
    have ha : (tripleCharges (sourceA466 + difference 4 0) (sourceB466 + difference 0 4) sourceC466) = raw8376 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8376; decide +kernel
    rw [ha]
    exact (canonical8376 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA466 + difference 4 1) (sourceB466 + difference 1 4) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2910) := by
    have ha : (tripleCharges (sourceA466 + difference 4 1) (sourceB466 + difference 1 4) sourceC466) = raw8377 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8377; decide +kernel
    rw [ha]
    exact (canonical8377 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA466 + difference 4 2) (sourceB466 + difference 2 4) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2910) := by
    have ha : (tripleCharges (sourceA466 + difference 4 2) (sourceB466 + difference 2 4) sourceC466) = raw8378 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8378; decide +kernel
    rw [ha]
    exact (canonical8378 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA466 + difference 4 3) (sourceB466 + difference 3 4) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2842) := by
    have ha : (tripleCharges (sourceA466 + difference 4 3) (sourceB466 + difference 3 4) sourceC466) = raw8379 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8379; decide +kernel
    rw [ha]
    exact (canonical8379 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA466 + difference 4 5) (sourceB466 + difference 5 4) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA466 + difference 4 5) (sourceB466 + difference 5 4) sourceC466) = raw8380 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8380; decide +kernel
    rw [ha]
    exact (canonical8380 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA466 + difference 5 0) (sourceB466 + difference 0 5) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1191) := by
    have ha : (tripleCharges (sourceA466 + difference 5 0) (sourceB466 + difference 0 5) sourceC466) = raw8381 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8381; decide +kernel
    rw [ha]
    exact (canonical8381 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA466 + difference 5 1) (sourceB466 + difference 1 5) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2393) := by
    have ha : (tripleCharges (sourceA466 + difference 5 1) (sourceB466 + difference 1 5) sourceC466) = raw8382 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8382; decide +kernel
    rw [ha]
    exact (canonical8382 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA466 + difference 5 2) (sourceB466 + difference 2 5) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2393) := by
    have ha : (tripleCharges (sourceA466 + difference 5 2) (sourceB466 + difference 2 5) sourceC466) = raw8383 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8383; decide +kernel
    rw [ha]
    exact (canonical8383 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA466 + difference 5 3) (sourceB466 + difference 3 5) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2408) := by
    have ha : (tripleCharges (sourceA466 + difference 5 3) (sourceB466 + difference 3 5) sourceC466) = raw8384 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8384; decide +kernel
    rw [ha]
    exact (canonical8384 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA466 + difference 5 4) (sourceB466 + difference 4 5) sourceC466) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA466 + difference 5 4) (sourceB466 + difference 4 5) sourceC466) = raw8385 := by
      apply Matrix.ext; unfold tripleCharges sourceA466 sourceB466 sourceC466 difference raw8385; decide +kernel
    rw [ha]
    exact (canonical8385 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA466 sourceB466 sourceC466
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm466, Integer.Sparse.eval]
  linarith only [hs]

def sourceA467 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB467 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC467 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceForm467 : Integer.Sparse Master := [(Sum.inr 2405, 2), (Sum.inr 2408, 1), (Sum.inr 2409, 1), (Sum.inr 2744, 1), (Sum.inr 2841, 2), (Sum.inr 2842, 1), (Sum.inr 3055, 1), (Sum.inr 3246, 2), (Sum.inr 3247, 1), (Sum.inr 3306, 1), (Sum.inr 3358, 2), (Sum.inr 3535, 2), (Sum.inr 3548, 1), (Sum.inr 3549, 1), (Sum.inr 3559, 2), (Sum.inr 3565, 2), (Sum.inr 3573, 2), (Sum.inr 3583, 1), (Sum.inr 3862, 1), (Sum.inr 3877, 2), (Sum.inr 3889, 1)]

theorem sourceEq467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm467 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA467 + difference 0 1) (sourceB467 + difference 1 0) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA467 + difference 0 1) (sourceB467 + difference 1 0) sourceC467) = raw8386 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8386; decide +kernel
    rw [ha]
    exact (canonical8386 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA467 + difference 0 2) (sourceB467 + difference 2 0) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA467 + difference 0 2) (sourceB467 + difference 2 0) sourceC467) = raw8387 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8387; decide +kernel
    rw [ha]
    exact (canonical8387 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA467 + difference 0 3) (sourceB467 + difference 3 0) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA467 + difference 0 3) (sourceB467 + difference 3 0) sourceC467) = raw8388 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8388; decide +kernel
    rw [ha]
    exact (canonical8388 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA467 + difference 0 4) (sourceB467 + difference 4 0) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA467 + difference 0 4) (sourceB467 + difference 4 0) sourceC467) = raw8389 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8389; decide +kernel
    rw [ha]
    exact (canonical8389 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA467 + difference 0 5) (sourceB467 + difference 5 0) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA467 + difference 0 5) (sourceB467 + difference 5 0) sourceC467) = raw8390 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8390; decide +kernel
    rw [ha]
    exact (canonical8390 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA467 + difference 1 0) (sourceB467 + difference 0 1) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3246) := by
    have ha : (tripleCharges (sourceA467 + difference 1 0) (sourceB467 + difference 0 1) sourceC467) = raw8391 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8391; decide +kernel
    rw [ha]
    exact (canonical8391 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA467 + difference 1 2) (sourceB467 + difference 2 1) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3559) := by
    have ha : (tripleCharges (sourceA467 + difference 1 2) (sourceB467 + difference 2 1) sourceC467) = raw8392 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8392; decide +kernel
    rw [ha]
    exact (canonical8392 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA467 + difference 1 3) (sourceB467 + difference 3 1) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2841) := by
    have ha : (tripleCharges (sourceA467 + difference 1 3) (sourceB467 + difference 3 1) sourceC467) = raw8393 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8393; decide +kernel
    rw [ha]
    exact (canonical8393 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA467 + difference 1 4) (sourceB467 + difference 4 1) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA467 + difference 1 4) (sourceB467 + difference 4 1) sourceC467) = raw8394 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8394; decide +kernel
    rw [ha]
    exact (canonical8394 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA467 + difference 1 5) (sourceB467 + difference 5 1) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA467 + difference 1 5) (sourceB467 + difference 5 1) sourceC467) = raw8395 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8395; decide +kernel
    rw [ha]
    exact (canonical8395 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA467 + difference 2 0) (sourceB467 + difference 0 2) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3246) := by
    have ha : (tripleCharges (sourceA467 + difference 2 0) (sourceB467 + difference 0 2) sourceC467) = raw8396 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8396; decide +kernel
    rw [ha]
    exact (canonical8396 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA467 + difference 2 1) (sourceB467 + difference 1 2) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3559) := by
    have ha : (tripleCharges (sourceA467 + difference 2 1) (sourceB467 + difference 1 2) sourceC467) = raw8397 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8397; decide +kernel
    rw [ha]
    exact (canonical8397 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA467 + difference 2 3) (sourceB467 + difference 3 2) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2841) := by
    have ha : (tripleCharges (sourceA467 + difference 2 3) (sourceB467 + difference 3 2) sourceC467) = raw8398 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8398; decide +kernel
    rw [ha]
    exact (canonical8398 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA467 + difference 2 4) (sourceB467 + difference 4 2) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA467 + difference 2 4) (sourceB467 + difference 4 2) sourceC467) = raw8399 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8399; decide +kernel
    rw [ha]
    exact (canonical8399 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA467 + difference 2 5) (sourceB467 + difference 5 2) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA467 + difference 2 5) (sourceB467 + difference 5 2) sourceC467) = raw8400 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8400; decide +kernel
    rw [ha]
    exact (canonical8400 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA467 + difference 3 0) (sourceB467 + difference 0 3) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA467 + difference 3 0) (sourceB467 + difference 0 3) sourceC467) = raw8401 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8401; decide +kernel
    rw [ha]
    exact (canonical8401 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA467 + difference 3 1) (sourceB467 + difference 1 3) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA467 + difference 3 1) (sourceB467 + difference 1 3) sourceC467) = raw8402 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8402; decide +kernel
    rw [ha]
    exact (canonical8402 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA467 + difference 3 2) (sourceB467 + difference 2 3) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA467 + difference 3 2) (sourceB467 + difference 2 3) sourceC467) = raw8403 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8403; decide +kernel
    rw [ha]
    exact (canonical8403 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA467 + difference 3 4) (sourceB467 + difference 4 3) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA467 + difference 3 4) (sourceB467 + difference 4 3) sourceC467) = raw8404 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8404; decide +kernel
    rw [ha]
    exact (canonical8404 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA467 + difference 3 5) (sourceB467 + difference 5 3) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA467 + difference 3 5) (sourceB467 + difference 5 3) sourceC467) = raw8405 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8405; decide +kernel
    rw [ha]
    exact (canonical8405 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA467 + difference 4 0) (sourceB467 + difference 0 4) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2409) := by
    have ha : (tripleCharges (sourceA467 + difference 4 0) (sourceB467 + difference 0 4) sourceC467) = raw8406 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8406; decide +kernel
    rw [ha]
    exact (canonical8406 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA467 + difference 4 1) (sourceB467 + difference 1 4) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2405) := by
    have ha : (tripleCharges (sourceA467 + difference 4 1) (sourceB467 + difference 1 4) sourceC467) = raw8407 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8407; decide +kernel
    rw [ha]
    exact (canonical8407 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA467 + difference 4 2) (sourceB467 + difference 2 4) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2405) := by
    have ha : (tripleCharges (sourceA467 + difference 4 2) (sourceB467 + difference 2 4) sourceC467) = raw8408 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8408; decide +kernel
    rw [ha]
    exact (canonical8408 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA467 + difference 4 3) (sourceB467 + difference 3 4) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2408) := by
    have ha : (tripleCharges (sourceA467 + difference 4 3) (sourceB467 + difference 3 4) sourceC467) = raw8409 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8409; decide +kernel
    rw [ha]
    exact (canonical8409 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA467 + difference 4 5) (sourceB467 + difference 5 4) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA467 + difference 4 5) (sourceB467 + difference 5 4) sourceC467) = raw8410 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8410; decide +kernel
    rw [ha]
    exact (canonical8410 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA467 + difference 5 0) (sourceB467 + difference 0 5) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3247) := by
    have ha : (tripleCharges (sourceA467 + difference 5 0) (sourceB467 + difference 0 5) sourceC467) = raw8411 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8411; decide +kernel
    rw [ha]
    exact (canonical8411 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA467 + difference 5 1) (sourceB467 + difference 1 5) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3358) := by
    have ha : (tripleCharges (sourceA467 + difference 5 1) (sourceB467 + difference 1 5) sourceC467) = raw8412 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8412; decide +kernel
    rw [ha]
    exact (canonical8412 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA467 + difference 5 2) (sourceB467 + difference 2 5) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3358) := by
    have ha : (tripleCharges (sourceA467 + difference 5 2) (sourceB467 + difference 2 5) sourceC467) = raw8413 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8413; decide +kernel
    rw [ha]
    exact (canonical8413 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA467 + difference 5 3) (sourceB467 + difference 3 5) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2842) := by
    have ha : (tripleCharges (sourceA467 + difference 5 3) (sourceB467 + difference 3 5) sourceC467) = raw8414 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8414; decide +kernel
    rw [ha]
    exact (canonical8414 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA467 + difference 5 4) (sourceB467 + difference 4 5) sourceC467) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA467 + difference 5 4) (sourceB467 + difference 4 5) sourceC467) = raw8415 := by
      apply Matrix.ext; unfold tripleCharges sourceA467 sourceB467 sourceC467 difference raw8415; decide +kernel
    rw [ha]
    exact (canonical8415 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA467 sourceB467 sourceC467
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm467, Integer.Sparse.eval]
  linarith only [hs]

def sourceA468 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB468 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC468 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceForm468 : Integer.Sparse Master := [(Sum.inr 2774, 2), (Sum.inr 3854, 2), (Sum.inr 3907, 2), (Sum.inr 4092, -1)]

theorem sourceEq468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm468 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA468 + difference 0 0) (sourceB468 + difference 0 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA468 + difference 0 0) (sourceB468 + difference 0 0) sourceC468) = raw8416 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8416; decide +kernel
    rw [ha]
    exact (canonical8416 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA468 + difference 0 1) (sourceB468 + difference 1 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA468 + difference 0 1) (sourceB468 + difference 1 0) sourceC468) = raw8417 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8417; decide +kernel
    rw [ha]
    exact (canonical8417 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA468 + difference 0 2) (sourceB468 + difference 2 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA468 + difference 0 2) (sourceB468 + difference 2 0) sourceC468) = raw8418 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8418; decide +kernel
    rw [ha]
    exact (canonical8418 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA468 + difference 0 3) (sourceB468 + difference 3 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA468 + difference 0 3) (sourceB468 + difference 3 0) sourceC468) = raw8419 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8419; decide +kernel
    rw [ha]
    exact (canonical8419 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA468 + difference 0 4) (sourceB468 + difference 4 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA468 + difference 0 4) (sourceB468 + difference 4 0) sourceC468) = raw8420 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8420; decide +kernel
    rw [ha]
    exact (canonical8420 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA468 + difference 0 5) (sourceB468 + difference 5 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA468 + difference 0 5) (sourceB468 + difference 5 0) sourceC468) = raw8421 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8421; decide +kernel
    rw [ha]
    exact (canonical8421 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA468 + sourceB468) sourceC468) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA468 + sourceB468) sourceC468) = raw8422 := by
      apply Matrix.ext; unfold doubleCharges sourceA468 sourceB468 sourceC468 raw8422; decide +kernel
    rw [ha]
    exact (canonical8422 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA468 sourceB468 sourceC468
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm468, Integer.Sparse.eval]
  linarith only [hs]

def sourceA469 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB469 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC469 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceForm469 : Integer.Sparse Master := [(Sum.inr 1277, 2), (Sum.inr 1279, 1), (Sum.inr 1283, 1), (Sum.inr 1295, 1), (Sum.inr 2774, 1), (Sum.inr 4092, -1)]

theorem sourceEq469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm469 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA469 + difference 0 0) (sourceB469 + difference 0 0) sourceC469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA469 + difference 0 0) (sourceB469 + difference 0 0) sourceC469) = raw8416 := by
      apply Matrix.ext; unfold tripleCharges sourceA469 sourceB469 sourceC469 difference raw8416; decide +kernel
    rw [ha]
    exact (canonical8416 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA469 + difference 1 0) (sourceB469 + difference 0 1) sourceC469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1277) := by
    have ha : (tripleCharges (sourceA469 + difference 1 0) (sourceB469 + difference 0 1) sourceC469) = raw8423 := by
      apply Matrix.ext; unfold tripleCharges sourceA469 sourceB469 sourceC469 difference raw8423; decide +kernel
    rw [ha]
    exact (canonical8423 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA469 + difference 2 0) (sourceB469 + difference 0 2) sourceC469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1277) := by
    have ha : (tripleCharges (sourceA469 + difference 2 0) (sourceB469 + difference 0 2) sourceC469) = raw8424 := by
      apply Matrix.ext; unfold tripleCharges sourceA469 sourceB469 sourceC469 difference raw8424; decide +kernel
    rw [ha]
    exact (canonical8424 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA469 + difference 3 0) (sourceB469 + difference 0 3) sourceC469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1295) := by
    have ha : (tripleCharges (sourceA469 + difference 3 0) (sourceB469 + difference 0 3) sourceC469) = raw8425 := by
      apply Matrix.ext; unfold tripleCharges sourceA469 sourceB469 sourceC469 difference raw8425; decide +kernel
    rw [ha]
    exact (canonical8425 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA469 + difference 4 0) (sourceB469 + difference 0 4) sourceC469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1283) := by
    have ha : (tripleCharges (sourceA469 + difference 4 0) (sourceB469 + difference 0 4) sourceC469) = raw8426 := by
      apply Matrix.ext; unfold tripleCharges sourceA469 sourceB469 sourceC469 difference raw8426; decide +kernel
    rw [ha]
    exact (canonical8426 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA469 + difference 5 0) (sourceB469 + difference 0 5) sourceC469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1279) := by
    have ha : (tripleCharges (sourceA469 + difference 5 0) (sourceB469 + difference 0 5) sourceC469) = raw8427 := by
      apply Matrix.ext; unfold tripleCharges sourceA469 sourceB469 sourceC469 difference raw8427; decide +kernel
    rw [ha]
    exact (canonical8427 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA469 + sourceB469) sourceC469) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA469 + sourceB469) sourceC469) = raw8422 := by
      apply Matrix.ext; unfold doubleCharges sourceA469 sourceB469 sourceC469 raw8422; decide +kernel
    rw [ha]
    exact (canonical8422 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA469 sourceB469 sourceC469
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm469, Integer.Sparse.eval]
  linarith only [hs]

def sourceA470 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB470 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC470 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceForm470 : Integer.Sparse Master := [(Sum.inr 2577, 1), (Sum.inr 2579, 1), (Sum.inr 2582, 1), (Sum.inr 2591, 1), (Sum.inr 2774, 1), (Sum.inr 3854, 1), (Sum.inr 4092, -1)]

theorem sourceEq470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm470 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA470 + difference 0 1) (sourceB470 + difference 1 0) sourceC470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA470 + difference 0 1) (sourceB470 + difference 1 0) sourceC470) = raw8417 := by
      apply Matrix.ext; unfold tripleCharges sourceA470 sourceB470 sourceC470 difference raw8417; decide +kernel
    rw [ha]
    exact (canonical8417 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA470 + difference 1 1) (sourceB470 + difference 1 1) sourceC470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA470 + difference 1 1) (sourceB470 + difference 1 1) sourceC470) = raw8416 := by
      apply Matrix.ext; unfold tripleCharges sourceA470 sourceB470 sourceC470 difference raw8416; decide +kernel
    rw [ha]
    exact (canonical8416 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA470 + difference 2 1) (sourceB470 + difference 1 2) sourceC470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2577) := by
    have ha : (tripleCharges (sourceA470 + difference 2 1) (sourceB470 + difference 1 2) sourceC470) = raw8428 := by
      apply Matrix.ext; unfold tripleCharges sourceA470 sourceB470 sourceC470 difference raw8428; decide +kernel
    rw [ha]
    exact (canonical8428 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA470 + difference 3 1) (sourceB470 + difference 1 3) sourceC470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA470 + difference 3 1) (sourceB470 + difference 1 3) sourceC470) = raw8429 := by
      apply Matrix.ext; unfold tripleCharges sourceA470 sourceB470 sourceC470 difference raw8429; decide +kernel
    rw [ha]
    exact (canonical8429 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA470 + difference 4 1) (sourceB470 + difference 1 4) sourceC470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2582) := by
    have ha : (tripleCharges (sourceA470 + difference 4 1) (sourceB470 + difference 1 4) sourceC470) = raw8430 := by
      apply Matrix.ext; unfold tripleCharges sourceA470 sourceB470 sourceC470 difference raw8430; decide +kernel
    rw [ha]
    exact (canonical8430 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA470 + difference 5 1) (sourceB470 + difference 1 5) sourceC470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2579) := by
    have ha : (tripleCharges (sourceA470 + difference 5 1) (sourceB470 + difference 1 5) sourceC470) = raw8431 := by
      apply Matrix.ext; unfold tripleCharges sourceA470 sourceB470 sourceC470 difference raw8431; decide +kernel
    rw [ha]
    exact (canonical8431 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA470 + sourceB470) sourceC470) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA470 + sourceB470) sourceC470) = raw8422 := by
      apply Matrix.ext; unfold doubleCharges sourceA470 sourceB470 sourceC470 raw8422; decide +kernel
    rw [ha]
    exact (canonical8422 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA470 sourceB470 sourceC470
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm470, Integer.Sparse.eval]
  linarith only [hs]

def sourceA471 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB471 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC471 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceForm471 : Integer.Sparse Master := [(Sum.inr 1295, 1), (Sum.inr 2591, 2), (Sum.inr 2743, 1), (Sum.inr 2774, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

theorem sourceEq471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm471 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA471 + difference 3 0) (sourceB471 + difference 0 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1295) := by
    have ha : (tripleCharges (sourceA471 + difference 3 0) (sourceB471 + difference 0 3) sourceC471) = raw8425 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8425; decide +kernel
    rw [ha]
    exact (canonical8425 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA471 + difference 3 1) (sourceB471 + difference 1 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA471 + difference 3 1) (sourceB471 + difference 1 3) sourceC471) = raw8429 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8429; decide +kernel
    rw [ha]
    exact (canonical8429 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA471 + difference 3 2) (sourceB471 + difference 2 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA471 + difference 3 2) (sourceB471 + difference 2 3) sourceC471) = raw8432 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8432; decide +kernel
    rw [ha]
    exact (canonical8432 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA471 + difference 3 3) (sourceB471 + difference 3 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA471 + difference 3 3) (sourceB471 + difference 3 3) sourceC471) = raw8416 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8416; decide +kernel
    rw [ha]
    exact (canonical8416 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA471 + difference 3 4) (sourceB471 + difference 4 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA471 + difference 3 4) (sourceB471 + difference 4 3) sourceC471) = raw8433 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8433; decide +kernel
    rw [ha]
    exact (canonical8433 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA471 + difference 3 5) (sourceB471 + difference 5 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA471 + difference 3 5) (sourceB471 + difference 5 3) sourceC471) = raw8434 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8434; decide +kernel
    rw [ha]
    exact (canonical8434 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA471 + sourceB471) sourceC471) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA471 + sourceB471) sourceC471) = raw8422 := by
      apply Matrix.ext; unfold doubleCharges sourceA471 sourceB471 sourceC471 raw8422; decide +kernel
    rw [ha]
    exact (canonical8422 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA471 sourceB471 sourceC471
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm471, Integer.Sparse.eval]
  linarith only [hs]

def sourceA472 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB472 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC472 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm472 : Integer.Sparse Master := [(Sum.inr 4471, 2), (Sum.inr 4472, 1), (Sum.inr 4480, 1), (Sum.inr 4492, 1), (Sum.inr 5083, 2), (Sum.inr 5084, 2), (Sum.inr 5090, 2), (Sum.inr 5096, 2), (Sum.inr 5199, 2), (Sum.inr 5201, 1), (Sum.inr 5206, 1), (Sum.inr 5207, 1), (Sum.inr 5233, 2), (Sum.inr 5235, 1), (Sum.inr 5295, 1), (Sum.inr 5299, 2), (Sum.inr 5302, 1), (Sum.inr 5446, 2), (Sum.inr 5449, 1), (Sum.inr 5451, 1), (Sum.inr 5475, 1)]

theorem sourceEq472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm472 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA472 + difference 0 1) (sourceB472 + difference 1 0) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA472 + difference 0 1) (sourceB472 + difference 1 0) sourceC472) = raw8435 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8435; decide +kernel
    rw [ha]
    exact (canonical8435 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA472 + difference 0 2) (sourceB472 + difference 2 0) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA472 + difference 0 2) (sourceB472 + difference 2 0) sourceC472) = raw8436 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8436; decide +kernel
    rw [ha]
    exact (canonical8436 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA472 + difference 0 3) (sourceB472 + difference 3 0) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA472 + difference 0 3) (sourceB472 + difference 3 0) sourceC472) = raw8437 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8437; decide +kernel
    rw [ha]
    exact (canonical8437 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA472 + difference 0 4) (sourceB472 + difference 4 0) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA472 + difference 0 4) (sourceB472 + difference 4 0) sourceC472) = raw8438 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8438; decide +kernel
    rw [ha]
    exact (canonical8438 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA472 + difference 0 5) (sourceB472 + difference 5 0) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA472 + difference 0 5) (sourceB472 + difference 5 0) sourceC472) = raw8439 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8439; decide +kernel
    rw [ha]
    exact (canonical8439 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA472 + difference 1 0) (sourceB472 + difference 0 1) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4471) := by
    have ha : (tripleCharges (sourceA472 + difference 1 0) (sourceB472 + difference 0 1) sourceC472) = raw8440 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8440; decide +kernel
    rw [ha]
    exact (canonical8440 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA472 + difference 1 2) (sourceB472 + difference 2 1) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5083) := by
    have ha : (tripleCharges (sourceA472 + difference 1 2) (sourceB472 + difference 2 1) sourceC472) = raw8441 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8441; decide +kernel
    rw [ha]
    exact (canonical8441 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA472 + difference 1 3) (sourceB472 + difference 3 1) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA472 + difference 1 3) (sourceB472 + difference 3 1) sourceC472) = raw8442 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8442; decide +kernel
    rw [ha]
    exact (canonical8442 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA472 + difference 1 4) (sourceB472 + difference 4 1) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA472 + difference 1 4) (sourceB472 + difference 4 1) sourceC472) = raw8443 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8443; decide +kernel
    rw [ha]
    exact (canonical8443 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA472 + difference 1 5) (sourceB472 + difference 5 1) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA472 + difference 1 5) (sourceB472 + difference 5 1) sourceC472) = raw8444 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8444; decide +kernel
    rw [ha]
    exact (canonical8444 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA472 + difference 2 0) (sourceB472 + difference 0 2) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4471) := by
    have ha : (tripleCharges (sourceA472 + difference 2 0) (sourceB472 + difference 0 2) sourceC472) = raw8445 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8445; decide +kernel
    rw [ha]
    exact (canonical8445 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA472 + difference 2 1) (sourceB472 + difference 1 2) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5083) := by
    have ha : (tripleCharges (sourceA472 + difference 2 1) (sourceB472 + difference 1 2) sourceC472) = raw8446 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8446; decide +kernel
    rw [ha]
    exact (canonical8446 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA472 + difference 2 3) (sourceB472 + difference 3 2) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA472 + difference 2 3) (sourceB472 + difference 3 2) sourceC472) = raw8447 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8447; decide +kernel
    rw [ha]
    exact (canonical8447 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA472 + difference 2 4) (sourceB472 + difference 4 2) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA472 + difference 2 4) (sourceB472 + difference 4 2) sourceC472) = raw8448 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8448; decide +kernel
    rw [ha]
    exact (canonical8448 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA472 + difference 2 5) (sourceB472 + difference 5 2) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA472 + difference 2 5) (sourceB472 + difference 5 2) sourceC472) = raw8449 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8449; decide +kernel
    rw [ha]
    exact (canonical8449 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA472 + difference 3 0) (sourceB472 + difference 0 3) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4492) := by
    have ha : (tripleCharges (sourceA472 + difference 3 0) (sourceB472 + difference 0 3) sourceC472) = raw8450 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8450; decide +kernel
    rw [ha]
    exact (canonical8450 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA472 + difference 3 1) (sourceB472 + difference 1 3) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5096) := by
    have ha : (tripleCharges (sourceA472 + difference 3 1) (sourceB472 + difference 1 3) sourceC472) = raw8451 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8451; decide +kernel
    rw [ha]
    exact (canonical8451 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA472 + difference 3 2) (sourceB472 + difference 2 3) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5096) := by
    have ha : (tripleCharges (sourceA472 + difference 3 2) (sourceB472 + difference 2 3) sourceC472) = raw8452 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8452; decide +kernel
    rw [ha]
    exact (canonical8452 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA472 + difference 3 4) (sourceB472 + difference 4 3) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA472 + difference 3 4) (sourceB472 + difference 4 3) sourceC472) = raw8453 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8453; decide +kernel
    rw [ha]
    exact (canonical8453 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA472 + difference 3 5) (sourceB472 + difference 5 3) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA472 + difference 3 5) (sourceB472 + difference 5 3) sourceC472) = raw8454 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8454; decide +kernel
    rw [ha]
    exact (canonical8454 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA472 + difference 4 0) (sourceB472 + difference 0 4) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA472 + difference 4 0) (sourceB472 + difference 0 4) sourceC472) = raw8455 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8455; decide +kernel
    rw [ha]
    exact (canonical8455 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA472 + difference 4 1) (sourceB472 + difference 1 4) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA472 + difference 4 1) (sourceB472 + difference 1 4) sourceC472) = raw8456 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8456; decide +kernel
    rw [ha]
    exact (canonical8456 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA472 + difference 4 2) (sourceB472 + difference 2 4) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA472 + difference 4 2) (sourceB472 + difference 2 4) sourceC472) = raw8457 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8457; decide +kernel
    rw [ha]
    exact (canonical8457 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA472 + difference 4 3) (sourceB472 + difference 3 4) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA472 + difference 4 3) (sourceB472 + difference 3 4) sourceC472) = raw8458 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8458; decide +kernel
    rw [ha]
    exact (canonical8458 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA472 + difference 4 5) (sourceB472 + difference 5 4) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA472 + difference 4 5) (sourceB472 + difference 5 4) sourceC472) = raw8459 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8459; decide +kernel
    rw [ha]
    exact (canonical8459 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA472 + difference 5 0) (sourceB472 + difference 0 5) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4472) := by
    have ha : (tripleCharges (sourceA472 + difference 5 0) (sourceB472 + difference 0 5) sourceC472) = raw8460 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8460; decide +kernel
    rw [ha]
    exact (canonical8460 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA472 + difference 5 1) (sourceB472 + difference 1 5) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5084) := by
    have ha : (tripleCharges (sourceA472 + difference 5 1) (sourceB472 + difference 1 5) sourceC472) = raw8461 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8461; decide +kernel
    rw [ha]
    exact (canonical8461 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA472 + difference 5 2) (sourceB472 + difference 2 5) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5084) := by
    have ha : (tripleCharges (sourceA472 + difference 5 2) (sourceB472 + difference 2 5) sourceC472) = raw8462 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8462; decide +kernel
    rw [ha]
    exact (canonical8462 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA472 + difference 5 3) (sourceB472 + difference 3 5) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5201) := by
    have ha : (tripleCharges (sourceA472 + difference 5 3) (sourceB472 + difference 3 5) sourceC472) = raw8463 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8463; decide +kernel
    rw [ha]
    exact (canonical8463 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA472 + difference 5 4) (sourceB472 + difference 4 5) sourceC472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5235) := by
    have ha : (tripleCharges (sourceA472 + difference 5 4) (sourceB472 + difference 4 5) sourceC472) = raw8464 := by
      apply Matrix.ext; unfold tripleCharges sourceA472 sourceB472 sourceC472 difference raw8464; decide +kernel
    rw [ha]
    exact (canonical8464 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA472 sourceB472 sourceC472
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm472, Integer.Sparse.eval]
  linarith only [hs]

def sourceA473 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB473 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC473 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm473 : Integer.Sparse Master := [(Sum.inr 1054, 2), (Sum.inr 1055, 1), (Sum.inr 1063, 1), (Sum.inr 1076, 1), (Sum.inr 2491, 2), (Sum.inr 2492, 2), (Sum.inr 2499, 2), (Sum.inr 2506, 2), (Sum.inr 2633, 2), (Sum.inr 2635, 1), (Sum.inr 2644, 1), (Sum.inr 2678, 2), (Sum.inr 2680, 1), (Sum.inr 2687, 1), (Sum.inr 2773, 2), (Sum.inr 2776, 1), (Sum.inr 2781, 1), (Sum.inr 3881, 2), (Sum.inr 3886, 1), (Sum.inr 3888, 1), (Sum.inr 4004, 1)]

theorem sourceEq473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm473 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA473 + difference 0 1) (sourceB473 + difference 1 0) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA473 + difference 0 1) (sourceB473 + difference 1 0) sourceC473) = raw8465 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8465; decide +kernel
    rw [ha]
    exact (canonical8465 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA473 + difference 0 2) (sourceB473 + difference 2 0) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA473 + difference 0 2) (sourceB473 + difference 2 0) sourceC473) = raw8466 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8466; decide +kernel
    rw [ha]
    exact (canonical8466 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA473 + difference 0 3) (sourceB473 + difference 3 0) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4004) := by
    have ha : (tripleCharges (sourceA473 + difference 0 3) (sourceB473 + difference 3 0) sourceC473) = raw8467 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8467; decide +kernel
    rw [ha]
    exact (canonical8467 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA473 + difference 0 4) (sourceB473 + difference 4 0) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA473 + difference 0 4) (sourceB473 + difference 4 0) sourceC473) = raw8468 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8468; decide +kernel
    rw [ha]
    exact (canonical8468 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA473 + difference 0 5) (sourceB473 + difference 5 0) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA473 + difference 0 5) (sourceB473 + difference 5 0) sourceC473) = raw8469 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8469; decide +kernel
    rw [ha]
    exact (canonical8469 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA473 + difference 1 0) (sourceB473 + difference 0 1) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA473 + difference 1 0) (sourceB473 + difference 0 1) sourceC473) = raw8470 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8470; decide +kernel
    rw [ha]
    exact (canonical8470 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA473 + difference 1 2) (sourceB473 + difference 2 1) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2491) := by
    have ha : (tripleCharges (sourceA473 + difference 1 2) (sourceB473 + difference 2 1) sourceC473) = raw8471 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8471; decide +kernel
    rw [ha]
    exact (canonical8471 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA473 + difference 1 3) (sourceB473 + difference 3 1) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA473 + difference 1 3) (sourceB473 + difference 3 1) sourceC473) = raw8472 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8472; decide +kernel
    rw [ha]
    exact (canonical8472 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA473 + difference 1 4) (sourceB473 + difference 4 1) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA473 + difference 1 4) (sourceB473 + difference 4 1) sourceC473) = raw8473 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8473; decide +kernel
    rw [ha]
    exact (canonical8473 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA473 + difference 1 5) (sourceB473 + difference 5 1) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA473 + difference 1 5) (sourceB473 + difference 5 1) sourceC473) = raw8474 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8474; decide +kernel
    rw [ha]
    exact (canonical8474 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA473 + difference 2 0) (sourceB473 + difference 0 2) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA473 + difference 2 0) (sourceB473 + difference 0 2) sourceC473) = raw8475 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8475; decide +kernel
    rw [ha]
    exact (canonical8475 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA473 + difference 2 1) (sourceB473 + difference 1 2) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2491) := by
    have ha : (tripleCharges (sourceA473 + difference 2 1) (sourceB473 + difference 1 2) sourceC473) = raw8476 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8476; decide +kernel
    rw [ha]
    exact (canonical8476 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA473 + difference 2 3) (sourceB473 + difference 3 2) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA473 + difference 2 3) (sourceB473 + difference 3 2) sourceC473) = raw8477 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8477; decide +kernel
    rw [ha]
    exact (canonical8477 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA473 + difference 2 4) (sourceB473 + difference 4 2) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA473 + difference 2 4) (sourceB473 + difference 4 2) sourceC473) = raw8478 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8478; decide +kernel
    rw [ha]
    exact (canonical8478 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA473 + difference 2 5) (sourceB473 + difference 5 2) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA473 + difference 2 5) (sourceB473 + difference 5 2) sourceC473) = raw8479 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8479; decide +kernel
    rw [ha]
    exact (canonical8479 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA473 + difference 3 0) (sourceB473 + difference 0 3) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1076) := by
    have ha : (tripleCharges (sourceA473 + difference 3 0) (sourceB473 + difference 0 3) sourceC473) = raw8480 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8480; decide +kernel
    rw [ha]
    exact (canonical8480 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA473 + difference 3 1) (sourceB473 + difference 1 3) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2506) := by
    have ha : (tripleCharges (sourceA473 + difference 3 1) (sourceB473 + difference 1 3) sourceC473) = raw8481 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8481; decide +kernel
    rw [ha]
    exact (canonical8481 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA473 + difference 3 2) (sourceB473 + difference 2 3) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2506) := by
    have ha : (tripleCharges (sourceA473 + difference 3 2) (sourceB473 + difference 2 3) sourceC473) = raw8482 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8482; decide +kernel
    rw [ha]
    exact (canonical8482 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA473 + difference 3 4) (sourceB473 + difference 4 3) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA473 + difference 3 4) (sourceB473 + difference 4 3) sourceC473) = raw8483 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8483; decide +kernel
    rw [ha]
    exact (canonical8483 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA473 + difference 3 5) (sourceB473 + difference 5 3) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA473 + difference 3 5) (sourceB473 + difference 5 3) sourceC473) = raw8484 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8484; decide +kernel
    rw [ha]
    exact (canonical8484 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA473 + difference 4 0) (sourceB473 + difference 0 4) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1063) := by
    have ha : (tripleCharges (sourceA473 + difference 4 0) (sourceB473 + difference 0 4) sourceC473) = raw8485 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8485; decide +kernel
    rw [ha]
    exact (canonical8485 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA473 + difference 4 1) (sourceB473 + difference 1 4) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA473 + difference 4 1) (sourceB473 + difference 1 4) sourceC473) = raw8486 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8486; decide +kernel
    rw [ha]
    exact (canonical8486 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA473 + difference 4 2) (sourceB473 + difference 2 4) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA473 + difference 4 2) (sourceB473 + difference 2 4) sourceC473) = raw8487 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8487; decide +kernel
    rw [ha]
    exact (canonical8487 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA473 + difference 4 3) (sourceB473 + difference 3 4) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2644) := by
    have ha : (tripleCharges (sourceA473 + difference 4 3) (sourceB473 + difference 3 4) sourceC473) = raw8488 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8488; decide +kernel
    rw [ha]
    exact (canonical8488 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA473 + difference 4 5) (sourceB473 + difference 5 4) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA473 + difference 4 5) (sourceB473 + difference 5 4) sourceC473) = raw8489 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8489; decide +kernel
    rw [ha]
    exact (canonical8489 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA473 + difference 5 0) (sourceB473 + difference 0 5) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1055) := by
    have ha : (tripleCharges (sourceA473 + difference 5 0) (sourceB473 + difference 0 5) sourceC473) = raw8490 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8490; decide +kernel
    rw [ha]
    exact (canonical8490 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA473 + difference 5 1) (sourceB473 + difference 1 5) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2492) := by
    have ha : (tripleCharges (sourceA473 + difference 5 1) (sourceB473 + difference 1 5) sourceC473) = raw8491 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8491; decide +kernel
    rw [ha]
    exact (canonical8491 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA473 + difference 5 2) (sourceB473 + difference 2 5) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2492) := by
    have ha : (tripleCharges (sourceA473 + difference 5 2) (sourceB473 + difference 2 5) sourceC473) = raw8492 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8492; decide +kernel
    rw [ha]
    exact (canonical8492 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA473 + difference 5 3) (sourceB473 + difference 3 5) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2635) := by
    have ha : (tripleCharges (sourceA473 + difference 5 3) (sourceB473 + difference 3 5) sourceC473) = raw8493 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8493; decide +kernel
    rw [ha]
    exact (canonical8493 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA473 + difference 5 4) (sourceB473 + difference 4 5) sourceC473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2680) := by
    have ha : (tripleCharges (sourceA473 + difference 5 4) (sourceB473 + difference 4 5) sourceC473) = raw8494 := by
      apply Matrix.ext; unfold tripleCharges sourceA473 sourceB473 sourceC473 difference raw8494; decide +kernel
    rw [ha]
    exact (canonical8494 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA473 sourceB473 sourceC473
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm473, Integer.Sparse.eval]
  linarith only [hs]

def sourceA474 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB474 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC474 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm474 : Integer.Sparse Master := [(Sum.inr 1649, 2), (Sum.inr 1651, 1), (Sum.inr 1652, 1), (Sum.inr 1740, 1), (Sum.inr 2875, 2), (Sum.inr 2888, 1), (Sum.inr 3098, 1), (Sum.inr 3385, 2), (Sum.inr 3395, 2), (Sum.inr 3396, 1), (Sum.inr 3447, 2), (Sum.inr 3480, 2), (Sum.inr 3573, 2), (Sum.inr 3578, 2), (Sum.inr 3579, 1), (Sum.inr 3626, 1), (Sum.inr 3631, 1), (Sum.inr 3959, 2), (Sum.inr 3963, 1), (Sum.inr 3987, 1), (Sum.inr 4030, 1)]

theorem sourceEq474 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm474 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA474 + difference 0 1) (sourceB474 + difference 1 0) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA474 + difference 0 1) (sourceB474 + difference 1 0) sourceC474) = raw8495 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8495; decide +kernel
    rw [ha]
    exact (canonical8495 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA474 + difference 0 2) (sourceB474 + difference 2 0) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA474 + difference 0 2) (sourceB474 + difference 2 0) sourceC474) = raw8496 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8496; decide +kernel
    rw [ha]
    exact (canonical8496 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA474 + difference 0 3) (sourceB474 + difference 3 0) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA474 + difference 0 3) (sourceB474 + difference 3 0) sourceC474) = raw8497 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8497; decide +kernel
    rw [ha]
    exact (canonical8497 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA474 + difference 0 4) (sourceB474 + difference 4 0) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4030) := by
    have ha : (tripleCharges (sourceA474 + difference 0 4) (sourceB474 + difference 4 0) sourceC474) = raw8498 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8498; decide +kernel
    rw [ha]
    exact (canonical8498 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA474 + difference 0 5) (sourceB474 + difference 5 0) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA474 + difference 0 5) (sourceB474 + difference 5 0) sourceC474) = raw8499 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8499; decide +kernel
    rw [ha]
    exact (canonical8499 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA474 + difference 1 0) (sourceB474 + difference 0 1) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1649) := by
    have ha : (tripleCharges (sourceA474 + difference 1 0) (sourceB474 + difference 0 1) sourceC474) = raw8500 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8500; decide +kernel
    rw [ha]
    exact (canonical8500 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA474 + difference 1 2) (sourceB474 + difference 2 1) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3447) := by
    have ha : (tripleCharges (sourceA474 + difference 1 2) (sourceB474 + difference 2 1) sourceC474) = raw8501 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8501; decide +kernel
    rw [ha]
    exact (canonical8501 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA474 + difference 1 3) (sourceB474 + difference 3 1) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA474 + difference 1 3) (sourceB474 + difference 3 1) sourceC474) = raw8502 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8502; decide +kernel
    rw [ha]
    exact (canonical8502 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA474 + difference 1 4) (sourceB474 + difference 4 1) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA474 + difference 1 4) (sourceB474 + difference 4 1) sourceC474) = raw8503 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8503; decide +kernel
    rw [ha]
    exact (canonical8503 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA474 + difference 1 5) (sourceB474 + difference 5 1) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA474 + difference 1 5) (sourceB474 + difference 5 1) sourceC474) = raw8504 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8504; decide +kernel
    rw [ha]
    exact (canonical8504 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA474 + difference 2 0) (sourceB474 + difference 0 2) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1649) := by
    have ha : (tripleCharges (sourceA474 + difference 2 0) (sourceB474 + difference 0 2) sourceC474) = raw8505 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8505; decide +kernel
    rw [ha]
    exact (canonical8505 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA474 + difference 2 1) (sourceB474 + difference 1 2) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3447) := by
    have ha : (tripleCharges (sourceA474 + difference 2 1) (sourceB474 + difference 1 2) sourceC474) = raw8506 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8506; decide +kernel
    rw [ha]
    exact (canonical8506 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA474 + difference 2 3) (sourceB474 + difference 3 2) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA474 + difference 2 3) (sourceB474 + difference 3 2) sourceC474) = raw8507 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8507; decide +kernel
    rw [ha]
    exact (canonical8507 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA474 + difference 2 4) (sourceB474 + difference 4 2) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA474 + difference 2 4) (sourceB474 + difference 4 2) sourceC474) = raw8508 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8508; decide +kernel
    rw [ha]
    exact (canonical8508 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA474 + difference 2 5) (sourceB474 + difference 5 2) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA474 + difference 2 5) (sourceB474 + difference 5 2) sourceC474) = raw8509 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8509; decide +kernel
    rw [ha]
    exact (canonical8509 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA474 + difference 3 0) (sourceB474 + difference 0 3) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1651) := by
    have ha : (tripleCharges (sourceA474 + difference 3 0) (sourceB474 + difference 0 3) sourceC474) = raw8510 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8510; decide +kernel
    rw [ha]
    exact (canonical8510 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA474 + difference 3 1) (sourceB474 + difference 1 3) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2875) := by
    have ha : (tripleCharges (sourceA474 + difference 3 1) (sourceB474 + difference 1 3) sourceC474) = raw8511 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8511; decide +kernel
    rw [ha]
    exact (canonical8511 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA474 + difference 3 2) (sourceB474 + difference 2 3) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2875) := by
    have ha : (tripleCharges (sourceA474 + difference 3 2) (sourceB474 + difference 2 3) sourceC474) = raw8512 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8512; decide +kernel
    rw [ha]
    exact (canonical8512 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA474 + difference 3 4) (sourceB474 + difference 4 3) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA474 + difference 3 4) (sourceB474 + difference 4 3) sourceC474) = raw8513 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8513; decide +kernel
    rw [ha]
    exact (canonical8513 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA474 + difference 3 5) (sourceB474 + difference 5 3) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA474 + difference 3 5) (sourceB474 + difference 5 3) sourceC474) = raw8514 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8514; decide +kernel
    rw [ha]
    exact (canonical8514 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA474 + difference 4 0) (sourceB474 + difference 0 4) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA474 + difference 4 0) (sourceB474 + difference 0 4) sourceC474) = raw8515 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8515; decide +kernel
    rw [ha]
    exact (canonical8515 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA474 + difference 4 1) (sourceB474 + difference 1 4) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA474 + difference 4 1) (sourceB474 + difference 1 4) sourceC474) = raw8516 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8516; decide +kernel
    rw [ha]
    exact (canonical8516 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA474 + difference 4 2) (sourceB474 + difference 2 4) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA474 + difference 4 2) (sourceB474 + difference 2 4) sourceC474) = raw8517 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8517; decide +kernel
    rw [ha]
    exact (canonical8517 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA474 + difference 4 3) (sourceB474 + difference 3 4) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA474 + difference 4 3) (sourceB474 + difference 3 4) sourceC474) = raw8518 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8518; decide +kernel
    rw [ha]
    exact (canonical8518 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA474 + difference 4 5) (sourceB474 + difference 5 4) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA474 + difference 4 5) (sourceB474 + difference 5 4) sourceC474) = raw8519 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8519; decide +kernel
    rw [ha]
    exact (canonical8519 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA474 + difference 5 0) (sourceB474 + difference 0 5) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1652) := by
    have ha : (tripleCharges (sourceA474 + difference 5 0) (sourceB474 + difference 0 5) sourceC474) = raw8520 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8520; decide +kernel
    rw [ha]
    exact (canonical8520 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA474 + difference 5 1) (sourceB474 + difference 1 5) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3385) := by
    have ha : (tripleCharges (sourceA474 + difference 5 1) (sourceB474 + difference 1 5) sourceC474) = raw8521 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8521; decide +kernel
    rw [ha]
    exact (canonical8521 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA474 + difference 5 2) (sourceB474 + difference 2 5) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3385) := by
    have ha : (tripleCharges (sourceA474 + difference 5 2) (sourceB474 + difference 2 5) sourceC474) = raw8522 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8522; decide +kernel
    rw [ha]
    exact (canonical8522 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA474 + difference 5 3) (sourceB474 + difference 3 5) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3579) := by
    have ha : (tripleCharges (sourceA474 + difference 5 3) (sourceB474 + difference 3 5) sourceC474) = raw8523 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8523; decide +kernel
    rw [ha]
    exact (canonical8523 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA474 + difference 5 4) (sourceB474 + difference 4 5) sourceC474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3396) := by
    have ha : (tripleCharges (sourceA474 + difference 5 4) (sourceB474 + difference 4 5) sourceC474) = raw8524 := by
      apply Matrix.ext; unfold tripleCharges sourceA474 sourceB474 sourceC474 difference raw8524; decide +kernel
    rw [ha]
    exact (canonical8524 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA474 sourceB474 sourceC474
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm474, Integer.Sparse.eval]
  linarith only [hs]

def sourceA475 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB475 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC475 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm475 : Integer.Sparse Master := [(Sum.inr 3055, 1), (Sum.inr 3884, 2), (Sum.inr 3886, 1), (Sum.inr 3913, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

theorem sourceEq475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm475 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA475 + difference 0 0) (sourceB475 + difference 0 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA475 + difference 0 0) (sourceB475 + difference 0 0) sourceC475) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA475 + difference 0 1) (sourceB475 + difference 1 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA475 + difference 0 1) (sourceB475 + difference 1 0) sourceC475) = raw8526 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8526; decide +kernel
    rw [ha]
    exact (canonical8526 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA475 + difference 0 2) (sourceB475 + difference 2 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA475 + difference 0 2) (sourceB475 + difference 2 0) sourceC475) = raw8527 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8527; decide +kernel
    rw [ha]
    exact (canonical8527 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA475 + difference 0 3) (sourceB475 + difference 3 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA475 + difference 0 3) (sourceB475 + difference 3 0) sourceC475) = raw8528 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8528; decide +kernel
    rw [ha]
    exact (canonical8528 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA475 + difference 0 4) (sourceB475 + difference 4 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA475 + difference 0 4) (sourceB475 + difference 4 0) sourceC475) = raw8529 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8529; decide +kernel
    rw [ha]
    exact (canonical8529 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA475 + difference 0 5) (sourceB475 + difference 5 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA475 + difference 0 5) (sourceB475 + difference 5 0) sourceC475) = raw8530 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8530; decide +kernel
    rw [ha]
    exact (canonical8530 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA475 + sourceB475) sourceC475) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA475 + sourceB475) sourceC475) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA475 sourceB475 sourceC475 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA475 sourceB475 sourceC475
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm475, Integer.Sparse.eval]
  linarith only [hs]

def sourceA476 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB476 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC476 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm476 : Integer.Sparse Master := [(Sum.inr 1368, 2), (Sum.inr 1373, 1), (Sum.inr 1375, 1), (Sum.inr 1437, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

theorem sourceEq476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm476 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA476 + difference 0 0) (sourceB476 + difference 0 0) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA476 + difference 0 0) (sourceB476 + difference 0 0) sourceC476) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA476 + difference 1 0) (sourceB476 + difference 0 1) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1368) := by
    have ha : (tripleCharges (sourceA476 + difference 1 0) (sourceB476 + difference 0 1) sourceC476) = raw8532 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8532; decide +kernel
    rw [ha]
    exact (canonical8532 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA476 + difference 2 0) (sourceB476 + difference 0 2) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1368) := by
    have ha : (tripleCharges (sourceA476 + difference 2 0) (sourceB476 + difference 0 2) sourceC476) = raw8533 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8533; decide +kernel
    rw [ha]
    exact (canonical8533 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA476 + difference 3 0) (sourceB476 + difference 0 3) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1437) := by
    have ha : (tripleCharges (sourceA476 + difference 3 0) (sourceB476 + difference 0 3) sourceC476) = raw8534 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8534; decide +kernel
    rw [ha]
    exact (canonical8534 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA476 + difference 4 0) (sourceB476 + difference 0 4) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA476 + difference 4 0) (sourceB476 + difference 0 4) sourceC476) = raw8535 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8535; decide +kernel
    rw [ha]
    exact (canonical8535 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA476 + difference 5 0) (sourceB476 + difference 0 5) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1373) := by
    have ha : (tripleCharges (sourceA476 + difference 5 0) (sourceB476 + difference 0 5) sourceC476) = raw8536 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8536; decide +kernel
    rw [ha]
    exact (canonical8536 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA476 + sourceB476) sourceC476) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA476 + sourceB476) sourceC476) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA476 sourceB476 sourceC476 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA476 sourceB476 sourceC476
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm476, Integer.Sparse.eval]
  linarith only [hs]

def sourceA477 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB477 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC477 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm477 : Integer.Sparse Master := [(Sum.inr 1368, 1), (Sum.inr 2882, 1), (Sum.inr 2975, 1), (Sum.inr 3044, 1), (Sum.inr 3051, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

theorem sourceEq477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm477 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA477 + difference 1 0) (sourceB477 + difference 0 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1368) := by
    have ha : (tripleCharges (sourceA477 + difference 1 0) (sourceB477 + difference 0 1) sourceC477) = raw8532 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8532; decide +kernel
    rw [ha]
    exact (canonical8532 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA477 + difference 1 1) (sourceB477 + difference 1 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA477 + difference 1 1) (sourceB477 + difference 1 1) sourceC477) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA477 + difference 1 2) (sourceB477 + difference 2 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2975) := by
    have ha : (tripleCharges (sourceA477 + difference 1 2) (sourceB477 + difference 2 1) sourceC477) = raw8537 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8537; decide +kernel
    rw [ha]
    exact (canonical8537 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA477 + difference 1 3) (sourceB477 + difference 3 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA477 + difference 1 3) (sourceB477 + difference 3 1) sourceC477) = raw8538 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8538; decide +kernel
    rw [ha]
    exact (canonical8538 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA477 + difference 1 4) (sourceB477 + difference 4 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA477 + difference 1 4) (sourceB477 + difference 4 1) sourceC477) = raw8539 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8539; decide +kernel
    rw [ha]
    exact (canonical8539 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA477 + difference 1 5) (sourceB477 + difference 5 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA477 + difference 1 5) (sourceB477 + difference 5 1) sourceC477) = raw8540 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8540; decide +kernel
    rw [ha]
    exact (canonical8540 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA477 + sourceB477) sourceC477) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA477 + sourceB477) sourceC477) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA477 sourceB477 sourceC477 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA477 sourceB477 sourceC477
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm477, Integer.Sparse.eval]
  linarith only [hs]

def sourceA478 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB478 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC478 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm478 : Integer.Sparse Master := [(Sum.inr 2639, 1), (Sum.inr 2871, 1), (Sum.inr 2975, 1), (Sum.inr 2979, 1), (Sum.inr 3055, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

theorem sourceEq478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm478 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA478 + difference 0 1) (sourceB478 + difference 1 0) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA478 + difference 0 1) (sourceB478 + difference 1 0) sourceC478) = raw8526 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8526; decide +kernel
    rw [ha]
    exact (canonical8526 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA478 + difference 1 1) (sourceB478 + difference 1 1) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA478 + difference 1 1) (sourceB478 + difference 1 1) sourceC478) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA478 + difference 2 1) (sourceB478 + difference 1 2) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2975) := by
    have ha : (tripleCharges (sourceA478 + difference 2 1) (sourceB478 + difference 1 2) sourceC478) = raw8541 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8541; decide +kernel
    rw [ha]
    exact (canonical8541 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA478 + difference 3 1) (sourceB478 + difference 1 3) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2639) := by
    have ha : (tripleCharges (sourceA478 + difference 3 1) (sourceB478 + difference 1 3) sourceC478) = raw8542 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8542; decide +kernel
    rw [ha]
    exact (canonical8542 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA478 + difference 4 1) (sourceB478 + difference 1 4) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA478 + difference 4 1) (sourceB478 + difference 1 4) sourceC478) = raw8543 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8543; decide +kernel
    rw [ha]
    exact (canonical8543 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA478 + difference 5 1) (sourceB478 + difference 1 5) sourceC478) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2871) := by
    have ha : (tripleCharges (sourceA478 + difference 5 1) (sourceB478 + difference 1 5) sourceC478) = raw8544 := by
      apply Matrix.ext; unfold tripleCharges sourceA478 sourceB478 sourceC478 difference raw8544; decide +kernel
    rw [ha]
    exact (canonical8544 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA478 + sourceB478) sourceC478) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA478 + sourceB478) sourceC478) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA478 sourceB478 sourceC478 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA478 sourceB478 sourceC478
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm478, Integer.Sparse.eval]
  linarith only [hs]

def sourceA479 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB479 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC479 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm479 : Integer.Sparse Master := [(Sum.inr 2882, 2), (Sum.inr 2886, 1), (Sum.inr 2889, 1), (Sum.inr 3055, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

theorem sourceEq479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm479 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA479 + difference 0 3) (sourceB479 + difference 3 0) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA479 + difference 0 3) (sourceB479 + difference 3 0) sourceC479) = raw8528 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8528; decide +kernel
    rw [ha]
    exact (canonical8528 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA479 + difference 1 3) (sourceB479 + difference 3 1) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA479 + difference 1 3) (sourceB479 + difference 3 1) sourceC479) = raw8538 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8538; decide +kernel
    rw [ha]
    exact (canonical8538 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA479 + difference 2 3) (sourceB479 + difference 3 2) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA479 + difference 2 3) (sourceB479 + difference 3 2) sourceC479) = raw8545 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8545; decide +kernel
    rw [ha]
    exact (canonical8545 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA479 + difference 3 3) (sourceB479 + difference 3 3) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA479 + difference 3 3) (sourceB479 + difference 3 3) sourceC479) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA479 + difference 4 3) (sourceB479 + difference 3 4) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA479 + difference 4 3) (sourceB479 + difference 3 4) sourceC479) = raw8546 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8546; decide +kernel
    rw [ha]
    exact (canonical8546 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA479 + difference 5 3) (sourceB479 + difference 3 5) sourceC479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2886) := by
    have ha : (tripleCharges (sourceA479 + difference 5 3) (sourceB479 + difference 3 5) sourceC479) = raw8547 := by
      apply Matrix.ext; unfold tripleCharges sourceA479 sourceB479 sourceC479 difference raw8547; decide +kernel
    rw [ha]
    exact (canonical8547 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA479 + sourceB479) sourceC479) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA479 + sourceB479) sourceC479) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA479 sourceB479 sourceC479 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA479 sourceB479 sourceC479
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm479, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
