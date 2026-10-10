import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical164
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical167
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical168

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1344 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1344 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1344 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1344 : Integer.Sparse Master := [(Sum.inr 4253, 2), (Sum.inr 4269, 1), (Sum.inr 4270, 1), (Sum.inr 4276, 1), (Sum.inr 4391, 2), (Sum.inr 4401, 2), (Sum.inr 4402, 2), (Sum.inr 4410, 2), (Sum.inr 4440, 2), (Sum.inr 4442, 2), (Sum.inr 4460, 1), (Sum.inr 4463, 2), (Sum.inr 4464, 1), (Sum.inr 4476, 1), (Sum.inr 4478, 1), (Sum.inr 4505, 1), (Sum.inr 4507, 1), (Sum.inr 4591, 2), (Sum.inr 4605, 1), (Sum.inr 4608, 1), (Sum.inr 4625, 1)]

theorem sourceEq1344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1344 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1344 + difference 0 1) (sourceB1344 + difference 1 0) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1344 + difference 0 1) (sourceB1344 + difference 1 0) sourceC1344) = raw20438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw20438; decide +kernel
    rw [ha]
    exact (canonical20438 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1344 + difference 0 2) (sourceB1344 + difference 2 0) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1344 + difference 0 2) (sourceB1344 + difference 2 0) sourceC1344) = raw21291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21291; decide +kernel
    rw [ha]
    exact (canonical21291 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1344 + difference 0 3) (sourceB1344 + difference 3 0) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1344 + difference 0 3) (sourceB1344 + difference 3 0) sourceC1344) = raw20798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw20798; decide +kernel
    rw [ha]
    exact (canonical20798 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1344 + difference 0 4) (sourceB1344 + difference 4 0) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1344 + difference 0 4) (sourceB1344 + difference 4 0) sourceC1344) = raw20423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw20423; decide +kernel
    rw [ha]
    exact (canonical20423 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1344 + difference 0 5) (sourceB1344 + difference 5 0) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1344 + difference 0 5) (sourceB1344 + difference 5 0) sourceC1344) = raw21292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21292; decide +kernel
    rw [ha]
    exact (canonical21292 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1344 + difference 1 0) (sourceB1344 + difference 0 1) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA1344 + difference 1 0) (sourceB1344 + difference 0 1) sourceC1344) = raw21293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21293; decide +kernel
    rw [ha]
    exact (canonical21293 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1344 + difference 1 2) (sourceB1344 + difference 2 1) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4410) := by
    have ha : (tripleCharges (sourceA1344 + difference 1 2) (sourceB1344 + difference 2 1) sourceC1344) = raw21294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21294; decide +kernel
    rw [ha]
    exact (canonical21294 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1344 + difference 1 3) (sourceB1344 + difference 3 1) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4410) := by
    have ha : (tripleCharges (sourceA1344 + difference 1 3) (sourceB1344 + difference 3 1) sourceC1344) = raw21295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21295; decide +kernel
    rw [ha]
    exact (canonical21295 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1344 + difference 1 4) (sourceB1344 + difference 4 1) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA1344 + difference 1 4) (sourceB1344 + difference 4 1) sourceC1344) = raw21296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21296; decide +kernel
    rw [ha]
    exact (canonical21296 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1344 + difference 1 5) (sourceB1344 + difference 5 1) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA1344 + difference 1 5) (sourceB1344 + difference 5 1) sourceC1344) = raw21297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21297; decide +kernel
    rw [ha]
    exact (canonical21297 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1344 + difference 2 0) (sourceB1344 + difference 0 2) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA1344 + difference 2 0) (sourceB1344 + difference 0 2) sourceC1344) = raw21298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21298; decide +kernel
    rw [ha]
    exact (canonical21298 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1344 + difference 2 1) (sourceB1344 + difference 1 2) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1344 + difference 2 1) (sourceB1344 + difference 1 2) sourceC1344) = raw21299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21299; decide +kernel
    rw [ha]
    exact (canonical21299 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1344 + difference 2 3) (sourceB1344 + difference 3 2) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4391) := by
    have ha : (tripleCharges (sourceA1344 + difference 2 3) (sourceB1344 + difference 3 2) sourceC1344) = raw21300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21300; decide +kernel
    rw [ha]
    exact (canonical21300 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1344 + difference 2 4) (sourceB1344 + difference 4 2) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1344 + difference 2 4) (sourceB1344 + difference 4 2) sourceC1344) = raw21301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21301; decide +kernel
    rw [ha]
    exact (canonical21301 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1344 + difference 2 5) (sourceB1344 + difference 5 2) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA1344 + difference 2 5) (sourceB1344 + difference 5 2) sourceC1344) = raw21302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21302; decide +kernel
    rw [ha]
    exact (canonical21302 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1344 + difference 3 0) (sourceB1344 + difference 0 3) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA1344 + difference 3 0) (sourceB1344 + difference 0 3) sourceC1344) = raw21303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21303; decide +kernel
    rw [ha]
    exact (canonical21303 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1344 + difference 3 1) (sourceB1344 + difference 1 3) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1344 + difference 3 1) (sourceB1344 + difference 1 3) sourceC1344) = raw21304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21304; decide +kernel
    rw [ha]
    exact (canonical21304 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1344 + difference 3 2) (sourceB1344 + difference 2 3) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4391) := by
    have ha : (tripleCharges (sourceA1344 + difference 3 2) (sourceB1344 + difference 2 3) sourceC1344) = raw21305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21305; decide +kernel
    rw [ha]
    exact (canonical21305 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1344 + difference 3 4) (sourceB1344 + difference 4 3) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1344 + difference 3 4) (sourceB1344 + difference 4 3) sourceC1344) = raw21306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21306; decide +kernel
    rw [ha]
    exact (canonical21306 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1344 + difference 3 5) (sourceB1344 + difference 5 3) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA1344 + difference 3 5) (sourceB1344 + difference 5 3) sourceC1344) = raw21307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21307; decide +kernel
    rw [ha]
    exact (canonical21307 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1344 + difference 4 0) (sourceB1344 + difference 0 4) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1344 + difference 4 0) (sourceB1344 + difference 0 4) sourceC1344) = raw21308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21308; decide +kernel
    rw [ha]
    exact (canonical21308 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1344 + difference 4 1) (sourceB1344 + difference 1 4) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1344 + difference 4 1) (sourceB1344 + difference 1 4) sourceC1344) = raw21309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21309; decide +kernel
    rw [ha]
    exact (canonical21309 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1344 + difference 4 2) (sourceB1344 + difference 2 4) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA1344 + difference 4 2) (sourceB1344 + difference 2 4) sourceC1344) = raw21310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21310; decide +kernel
    rw [ha]
    exact (canonical21310 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1344 + difference 4 3) (sourceB1344 + difference 3 4) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA1344 + difference 4 3) (sourceB1344 + difference 3 4) sourceC1344) = raw21311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21311; decide +kernel
    rw [ha]
    exact (canonical21311 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1344 + difference 4 5) (sourceB1344 + difference 5 4) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1344 + difference 4 5) (sourceB1344 + difference 5 4) sourceC1344) = raw21312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21312; decide +kernel
    rw [ha]
    exact (canonical21312 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1344 + difference 5 0) (sourceB1344 + difference 0 5) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1344 + difference 5 0) (sourceB1344 + difference 0 5) sourceC1344) = raw21313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21313; decide +kernel
    rw [ha]
    exact (canonical21313 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1344 + difference 5 1) (sourceB1344 + difference 1 5) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1344 + difference 5 1) (sourceB1344 + difference 1 5) sourceC1344) = raw20434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw20434; decide +kernel
    rw [ha]
    exact (canonical20434 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1344 + difference 5 2) (sourceB1344 + difference 2 5) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1344 + difference 5 2) (sourceB1344 + difference 2 5) sourceC1344) = raw21314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw21314; decide +kernel
    rw [ha]
    exact (canonical21314 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1344 + difference 5 3) (sourceB1344 + difference 3 5) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1344 + difference 5 3) (sourceB1344 + difference 3 5) sourceC1344) = raw20795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw20795; decide +kernel
    rw [ha]
    exact (canonical20795 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1344 + difference 5 4) (sourceB1344 + difference 4 5) sourceC1344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1344 + difference 5 4) (sourceB1344 + difference 4 5) sourceC1344) = raw20419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1344 sourceB1344 sourceC1344 difference raw20419; decide +kernel
    rw [ha]
    exact (canonical20419 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1344 sourceB1344 sourceC1344
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1344, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1345 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1345 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1345 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1345 : Integer.Sparse Master := [(Sum.inr 787, 2), (Sum.inr 812, 1), (Sum.inr 813, 1), (Sum.inr 828, 1), (Sum.inr 972, 2), (Sum.inr 982, 2), (Sum.inr 983, 2), (Sum.inr 991, 2), (Sum.inr 1022, 2), (Sum.inr 1024, 2), (Sum.inr 1043, 1), (Sum.inr 1046, 2), (Sum.inr 1047, 1), (Sum.inr 1059, 1), (Sum.inr 1061, 1), (Sum.inr 1089, 1), (Sum.inr 1091, 1), (Sum.inr 1217, 2), (Sum.inr 1269, 1), (Sum.inr 1271, 1), (Sum.inr 1307, 1)]

theorem sourceEq1345 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1345 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1345 + difference 0 1) (sourceB1345 + difference 1 0) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1345 + difference 0 1) (sourceB1345 + difference 1 0) sourceC1345) = raw20830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw20830; decide +kernel
    rw [ha]
    exact (canonical20830 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1345 + difference 0 2) (sourceB1345 + difference 2 0) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1345 + difference 0 2) (sourceB1345 + difference 2 0) sourceC1345) = raw21315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21315; decide +kernel
    rw [ha]
    exact (canonical21315 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1345 + difference 0 3) (sourceB1345 + difference 3 0) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1345 + difference 0 3) (sourceB1345 + difference 3 0) sourceC1345) = raw20821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw20821; decide +kernel
    rw [ha]
    exact (canonical20821 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1345 + difference 0 4) (sourceB1345 + difference 4 0) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1269) := by
    have ha : (tripleCharges (sourceA1345 + difference 0 4) (sourceB1345 + difference 4 0) sourceC1345) = raw21316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21316; decide +kernel
    rw [ha]
    exact (canonical21316 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1345 + difference 0 5) (sourceB1345 + difference 5 0) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1345 + difference 0 5) (sourceB1345 + difference 5 0) sourceC1345) = raw21317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21317; decide +kernel
    rw [ha]
    exact (canonical21317 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1345 + difference 1 0) (sourceB1345 + difference 0 1) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA1345 + difference 1 0) (sourceB1345 + difference 0 1) sourceC1345) = raw21318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21318; decide +kernel
    rw [ha]
    exact (canonical21318 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1345 + difference 1 2) (sourceB1345 + difference 2 1) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 991) := by
    have ha : (tripleCharges (sourceA1345 + difference 1 2) (sourceB1345 + difference 2 1) sourceC1345) = raw21319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21319; decide +kernel
    rw [ha]
    exact (canonical21319 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1345 + difference 1 3) (sourceB1345 + difference 3 1) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 991) := by
    have ha : (tripleCharges (sourceA1345 + difference 1 3) (sourceB1345 + difference 3 1) sourceC1345) = raw21320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21320; decide +kernel
    rw [ha]
    exact (canonical21320 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1345 + difference 1 4) (sourceB1345 + difference 4 1) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA1345 + difference 1 4) (sourceB1345 + difference 4 1) sourceC1345) = raw21321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21321; decide +kernel
    rw [ha]
    exact (canonical21321 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1345 + difference 1 5) (sourceB1345 + difference 5 1) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA1345 + difference 1 5) (sourceB1345 + difference 5 1) sourceC1345) = raw21322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21322; decide +kernel
    rw [ha]
    exact (canonical21322 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1345 + difference 2 0) (sourceB1345 + difference 0 2) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1345 + difference 2 0) (sourceB1345 + difference 0 2) sourceC1345) = raw21323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21323; decide +kernel
    rw [ha]
    exact (canonical21323 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1345 + difference 2 1) (sourceB1345 + difference 1 2) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1345 + difference 2 1) (sourceB1345 + difference 1 2) sourceC1345) = raw21324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21324; decide +kernel
    rw [ha]
    exact (canonical21324 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1345 + difference 2 3) (sourceB1345 + difference 3 2) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 972) := by
    have ha : (tripleCharges (sourceA1345 + difference 2 3) (sourceB1345 + difference 3 2) sourceC1345) = raw21325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21325; decide +kernel
    rw [ha]
    exact (canonical21325 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1345 + difference 2 4) (sourceB1345 + difference 4 2) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA1345 + difference 2 4) (sourceB1345 + difference 4 2) sourceC1345) = raw21326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21326; decide +kernel
    rw [ha]
    exact (canonical21326 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1345 + difference 2 5) (sourceB1345 + difference 5 2) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA1345 + difference 2 5) (sourceB1345 + difference 5 2) sourceC1345) = raw21327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21327; decide +kernel
    rw [ha]
    exact (canonical21327 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1345 + difference 3 0) (sourceB1345 + difference 0 3) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1345 + difference 3 0) (sourceB1345 + difference 0 3) sourceC1345) = raw21328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21328; decide +kernel
    rw [ha]
    exact (canonical21328 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1345 + difference 3 1) (sourceB1345 + difference 1 3) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1345 + difference 3 1) (sourceB1345 + difference 1 3) sourceC1345) = raw21329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21329; decide +kernel
    rw [ha]
    exact (canonical21329 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1345 + difference 3 2) (sourceB1345 + difference 2 3) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 972) := by
    have ha : (tripleCharges (sourceA1345 + difference 3 2) (sourceB1345 + difference 2 3) sourceC1345) = raw21330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21330; decide +kernel
    rw [ha]
    exact (canonical21330 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1345 + difference 3 4) (sourceB1345 + difference 4 3) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA1345 + difference 3 4) (sourceB1345 + difference 4 3) sourceC1345) = raw21331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21331; decide +kernel
    rw [ha]
    exact (canonical21331 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1345 + difference 3 5) (sourceB1345 + difference 5 3) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA1345 + difference 3 5) (sourceB1345 + difference 5 3) sourceC1345) = raw21332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21332; decide +kernel
    rw [ha]
    exact (canonical21332 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1345 + difference 4 0) (sourceB1345 + difference 0 4) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1345 + difference 4 0) (sourceB1345 + difference 0 4) sourceC1345) = raw21333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21333; decide +kernel
    rw [ha]
    exact (canonical21333 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1345 + difference 4 1) (sourceB1345 + difference 1 4) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1345 + difference 4 1) (sourceB1345 + difference 1 4) sourceC1345) = raw21334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21334; decide +kernel
    rw [ha]
    exact (canonical21334 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1345 + difference 4 2) (sourceB1345 + difference 2 4) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA1345 + difference 4 2) (sourceB1345 + difference 2 4) sourceC1345) = raw21335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21335; decide +kernel
    rw [ha]
    exact (canonical21335 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1345 + difference 4 3) (sourceB1345 + difference 3 4) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA1345 + difference 4 3) (sourceB1345 + difference 3 4) sourceC1345) = raw21336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21336; decide +kernel
    rw [ha]
    exact (canonical21336 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1345 + difference 4 5) (sourceB1345 + difference 5 4) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1345 + difference 4 5) (sourceB1345 + difference 5 4) sourceC1345) = raw21337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21337; decide +kernel
    rw [ha]
    exact (canonical21337 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1345 + difference 5 0) (sourceB1345 + difference 0 5) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1345 + difference 5 0) (sourceB1345 + difference 0 5) sourceC1345) = raw21338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21338; decide +kernel
    rw [ha]
    exact (canonical21338 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1345 + difference 5 1) (sourceB1345 + difference 1 5) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1089) := by
    have ha : (tripleCharges (sourceA1345 + difference 5 1) (sourceB1345 + difference 1 5) sourceC1345) = raw20827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw20827; decide +kernel
    rw [ha]
    exact (canonical20827 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1345 + difference 5 2) (sourceB1345 + difference 2 5) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1345 + difference 5 2) (sourceB1345 + difference 2 5) sourceC1345) = raw21339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21339; decide +kernel
    rw [ha]
    exact (canonical21339 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1345 + difference 5 3) (sourceB1345 + difference 3 5) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1345 + difference 5 3) (sourceB1345 + difference 3 5) sourceC1345) = raw20817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw20817; decide +kernel
    rw [ha]
    exact (canonical20817 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1345 + difference 5 4) (sourceB1345 + difference 4 5) sourceC1345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1345 + difference 5 4) (sourceB1345 + difference 4 5) sourceC1345) = raw21340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1345 sourceB1345 sourceC1345 difference raw21340; decide +kernel
    rw [ha]
    exact (canonical21340 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1345 sourceB1345 sourceC1345
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1345, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1346 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1346 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1346 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1346 : Integer.Sparse Master := [(Sum.inr 1215, 2), (Sum.inr 1239, 1), (Sum.inr 1242, 1), (Sum.inr 1304, 1), (Sum.inr 1359, 2), (Sum.inr 1369, 1), (Sum.inr 1372, 1), (Sum.inr 1378, 2), (Sum.inr 1385, 2), (Sum.inr 1388, 2), (Sum.inr 1394, 2), (Sum.inr 1397, 2), (Sum.inr 1408, 1), (Sum.inr 1413, 2), (Sum.inr 1416, 1), (Sum.inr 1445, 1), (Sum.inr 1450, 1), (Sum.inr 1469, 1), (Sum.inr 1476, 2), (Sum.inr 1481, 1), (Sum.inr 1484, 1)]

theorem sourceEq1346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1346 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1346 + difference 0 1) (sourceB1346 + difference 1 0) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA1346 + difference 0 1) (sourceB1346 + difference 1 0) sourceC1346) = raw20468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw20468; decide +kernel
    rw [ha]
    exact (canonical20468 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1346 + difference 0 2) (sourceB1346 + difference 2 0) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1346 + difference 0 2) (sourceB1346 + difference 2 0) sourceC1346) = raw21341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21341; decide +kernel
    rw [ha]
    exact (canonical21341 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1346 + difference 0 3) (sourceB1346 + difference 3 0) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1346 + difference 0 3) (sourceB1346 + difference 3 0) sourceC1346) = raw21342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21342; decide +kernel
    rw [ha]
    exact (canonical21342 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1346 + difference 0 4) (sourceB1346 + difference 4 0) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1346 + difference 0 4) (sourceB1346 + difference 4 0) sourceC1346) = raw20453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw20453; decide +kernel
    rw [ha]
    exact (canonical20453 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1346 + difference 0 5) (sourceB1346 + difference 5 0) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1346 + difference 0 5) (sourceB1346 + difference 5 0) sourceC1346) = raw21343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21343; decide +kernel
    rw [ha]
    exact (canonical21343 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1346 + difference 1 0) (sourceB1346 + difference 0 1) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1469) := by
    have ha : (tripleCharges (sourceA1346 + difference 1 0) (sourceB1346 + difference 0 1) sourceC1346) = raw21344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21344; decide +kernel
    rw [ha]
    exact (canonical21344 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1346 + difference 1 2) (sourceB1346 + difference 2 1) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1359) := by
    have ha : (tripleCharges (sourceA1346 + difference 1 2) (sourceB1346 + difference 2 1) sourceC1346) = raw21345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21345; decide +kernel
    rw [ha]
    exact (canonical21345 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1346 + difference 1 3) (sourceB1346 + difference 3 1) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1359) := by
    have ha : (tripleCharges (sourceA1346 + difference 1 3) (sourceB1346 + difference 3 1) sourceC1346) = raw21346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21346; decide +kernel
    rw [ha]
    exact (canonical21346 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1346 + difference 1 4) (sourceB1346 + difference 4 1) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA1346 + difference 1 4) (sourceB1346 + difference 4 1) sourceC1346) = raw21347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21347; decide +kernel
    rw [ha]
    exact (canonical21347 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1346 + difference 1 5) (sourceB1346 + difference 5 1) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA1346 + difference 1 5) (sourceB1346 + difference 5 1) sourceC1346) = raw21348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21348; decide +kernel
    rw [ha]
    exact (canonical21348 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1346 + difference 2 0) (sourceB1346 + difference 0 2) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1476) := by
    have ha : (tripleCharges (sourceA1346 + difference 2 0) (sourceB1346 + difference 0 2) sourceC1346) = raw21349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21349; decide +kernel
    rw [ha]
    exact (canonical21349 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1346 + difference 2 1) (sourceB1346 + difference 1 2) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA1346 + difference 2 1) (sourceB1346 + difference 1 2) sourceC1346) = raw21350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21350; decide +kernel
    rw [ha]
    exact (canonical21350 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1346 + difference 2 3) (sourceB1346 + difference 3 2) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1378) := by
    have ha : (tripleCharges (sourceA1346 + difference 2 3) (sourceB1346 + difference 3 2) sourceC1346) = raw21351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21351; decide +kernel
    rw [ha]
    exact (canonical21351 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1346 + difference 2 4) (sourceB1346 + difference 4 2) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1346 + difference 2 4) (sourceB1346 + difference 4 2) sourceC1346) = raw21352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21352; decide +kernel
    rw [ha]
    exact (canonical21352 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1346 + difference 2 5) (sourceB1346 + difference 5 2) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA1346 + difference 2 5) (sourceB1346 + difference 5 2) sourceC1346) = raw21353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21353; decide +kernel
    rw [ha]
    exact (canonical21353 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1346 + difference 3 0) (sourceB1346 + difference 0 3) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1476) := by
    have ha : (tripleCharges (sourceA1346 + difference 3 0) (sourceB1346 + difference 0 3) sourceC1346) = raw21354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21354; decide +kernel
    rw [ha]
    exact (canonical21354 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1346 + difference 3 1) (sourceB1346 + difference 1 3) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA1346 + difference 3 1) (sourceB1346 + difference 1 3) sourceC1346) = raw21355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21355; decide +kernel
    rw [ha]
    exact (canonical21355 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1346 + difference 3 2) (sourceB1346 + difference 2 3) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1378) := by
    have ha : (tripleCharges (sourceA1346 + difference 3 2) (sourceB1346 + difference 2 3) sourceC1346) = raw21356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21356; decide +kernel
    rw [ha]
    exact (canonical21356 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1346 + difference 3 4) (sourceB1346 + difference 4 3) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1346 + difference 3 4) (sourceB1346 + difference 4 3) sourceC1346) = raw21357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21357; decide +kernel
    rw [ha]
    exact (canonical21357 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1346 + difference 3 5) (sourceB1346 + difference 5 3) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA1346 + difference 3 5) (sourceB1346 + difference 5 3) sourceC1346) = raw21358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21358; decide +kernel
    rw [ha]
    exact (canonical21358 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1346 + difference 4 0) (sourceB1346 + difference 0 4) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1481) := by
    have ha : (tripleCharges (sourceA1346 + difference 4 0) (sourceB1346 + difference 0 4) sourceC1346) = raw21359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21359; decide +kernel
    rw [ha]
    exact (canonical21359 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1346 + difference 4 1) (sourceB1346 + difference 1 4) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1445) := by
    have ha : (tripleCharges (sourceA1346 + difference 4 1) (sourceB1346 + difference 1 4) sourceC1346) = raw21360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21360; decide +kernel
    rw [ha]
    exact (canonical21360 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1346 + difference 4 2) (sourceB1346 + difference 2 4) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1394) := by
    have ha : (tripleCharges (sourceA1346 + difference 4 2) (sourceB1346 + difference 2 4) sourceC1346) = raw21361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21361; decide +kernel
    rw [ha]
    exact (canonical21361 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1346 + difference 4 3) (sourceB1346 + difference 3 4) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1394) := by
    have ha : (tripleCharges (sourceA1346 + difference 4 3) (sourceB1346 + difference 3 4) sourceC1346) = raw21362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21362; decide +kernel
    rw [ha]
    exact (canonical21362 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1346 + difference 4 5) (sourceB1346 + difference 5 4) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA1346 + difference 4 5) (sourceB1346 + difference 5 4) sourceC1346) = raw21363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21363; decide +kernel
    rw [ha]
    exact (canonical21363 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1346 + difference 5 0) (sourceB1346 + difference 0 5) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1484) := by
    have ha : (tripleCharges (sourceA1346 + difference 5 0) (sourceB1346 + difference 0 5) sourceC1346) = raw21364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21364; decide +kernel
    rw [ha]
    exact (canonical21364 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1346 + difference 5 1) (sourceB1346 + difference 1 5) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1450) := by
    have ha : (tripleCharges (sourceA1346 + difference 5 1) (sourceB1346 + difference 1 5) sourceC1346) = raw20464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw20464; decide +kernel
    rw [ha]
    exact (canonical20464 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1346 + difference 5 2) (sourceB1346 + difference 2 5) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1397) := by
    have ha : (tripleCharges (sourceA1346 + difference 5 2) (sourceB1346 + difference 2 5) sourceC1346) = raw21365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21365; decide +kernel
    rw [ha]
    exact (canonical21365 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1346 + difference 5 3) (sourceB1346 + difference 3 5) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1397) := by
    have ha : (tripleCharges (sourceA1346 + difference 5 3) (sourceB1346 + difference 3 5) sourceC1346) = raw21366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw21366; decide +kernel
    rw [ha]
    exact (canonical21366 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1346 + difference 5 4) (sourceB1346 + difference 4 5) sourceC1346) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1346 + difference 5 4) (sourceB1346 + difference 4 5) sourceC1346) = raw20449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1346 sourceB1346 sourceC1346 difference raw20449; decide +kernel
    rw [ha]
    exact (canonical20449 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1346 sourceB1346 sourceC1346
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1346, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1347 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1347 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1347 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1347 : Integer.Sparse Master := [(Sum.inr 847, 2), (Sum.inr 851, 1), (Sum.inr 853, 1), (Sum.inr 857, 1), (Sum.inr 1750, 1), (Sum.inr 4070, -1)]

theorem sourceEq1347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1347 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1347 + difference 0 0) (sourceB1347 + difference 0 0) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1347 + difference 0 0) (sourceB1347 + difference 0 0) sourceC1347) = raw21367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21367; decide +kernel
    rw [ha]
    exact (canonical21367 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1347 + difference 1 0) (sourceB1347 + difference 0 1) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 857) := by
    have ha : (tripleCharges (sourceA1347 + difference 1 0) (sourceB1347 + difference 0 1) sourceC1347) = raw21368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21368; decide +kernel
    rw [ha]
    exact (canonical21368 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1347 + difference 2 0) (sourceB1347 + difference 0 2) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1347 + difference 2 0) (sourceB1347 + difference 0 2) sourceC1347) = raw21369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21369; decide +kernel
    rw [ha]
    exact (canonical21369 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1347 + difference 3 0) (sourceB1347 + difference 0 3) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1347 + difference 3 0) (sourceB1347 + difference 0 3) sourceC1347) = raw21370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21370; decide +kernel
    rw [ha]
    exact (canonical21370 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1347 + difference 4 0) (sourceB1347 + difference 0 4) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 853) := by
    have ha : (tripleCharges (sourceA1347 + difference 4 0) (sourceB1347 + difference 0 4) sourceC1347) = raw21371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21371; decide +kernel
    rw [ha]
    exact (canonical21371 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1347 + difference 5 0) (sourceB1347 + difference 0 5) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 851) := by
    have ha : (tripleCharges (sourceA1347 + difference 5 0) (sourceB1347 + difference 0 5) sourceC1347) = raw21372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21372; decide +kernel
    rw [ha]
    exact (canonical21372 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1347 + sourceB1347) sourceC1347) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1347 + sourceB1347) sourceC1347) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1347 sourceB1347 sourceC1347 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1347 sourceB1347 sourceC1347
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1347, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1348 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1348 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1348 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1348 : Integer.Sparse Master := [(Sum.inr 4151, 2), (Sum.inr 4156, 1), (Sum.inr 4160, 1), (Sum.inr 4177, 1), (Sum.inr 4326, 2), (Sum.inr 4330, 2), (Sum.inr 4334, 2), (Sum.inr 4346, 2), (Sum.inr 4365, 2), (Sum.inr 4370, 1), (Sum.inr 4373, 1), (Sum.inr 4457, 2), (Sum.inr 4460, 2), (Sum.inr 4466, 1), (Sum.inr 4468, 1), (Sum.inr 4498, 1), (Sum.inr 4505, 1), (Sum.inr 4804, 2), (Sum.inr 4868, 1), (Sum.inr 4894, 1), (Sum.inr 4897, 1)]

theorem sourceEq1348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1348 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1348 + difference 0 1) (sourceB1348 + difference 1 0) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA1348 + difference 0 1) (sourceB1348 + difference 1 0) sourceC1348) = raw11497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11497; decide +kernel
    rw [ha]
    exact (canonical11497 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1348 + difference 0 2) (sourceB1348 + difference 2 0) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1348 + difference 0 2) (sourceB1348 + difference 2 0) sourceC1348) = raw11498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11498; decide +kernel
    rw [ha]
    exact (canonical11498 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1348 + difference 0 3) (sourceB1348 + difference 3 0) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1348 + difference 0 3) (sourceB1348 + difference 3 0) sourceC1348) = raw11499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11499; decide +kernel
    rw [ha]
    exact (canonical11499 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1348 + difference 0 4) (sourceB1348 + difference 4 0) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1348 + difference 0 4) (sourceB1348 + difference 4 0) sourceC1348) = raw11500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11500; decide +kernel
    rw [ha]
    exact (canonical11500 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1348 + difference 0 5) (sourceB1348 + difference 5 0) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA1348 + difference 0 5) (sourceB1348 + difference 5 0) sourceC1348) = raw21373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21373; decide +kernel
    rw [ha]
    exact (canonical21373 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1348 + difference 1 0) (sourceB1348 + difference 0 1) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1348 + difference 1 0) (sourceB1348 + difference 0 1) sourceC1348) = raw21374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21374; decide +kernel
    rw [ha]
    exact (canonical21374 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1348 + difference 1 2) (sourceB1348 + difference 2 1) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1348 + difference 1 2) (sourceB1348 + difference 2 1) sourceC1348) = raw21375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21375; decide +kernel
    rw [ha]
    exact (canonical21375 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1348 + difference 1 3) (sourceB1348 + difference 3 1) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1348 + difference 1 3) (sourceB1348 + difference 3 1) sourceC1348) = raw21376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21376; decide +kernel
    rw [ha]
    exact (canonical21376 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1348 + difference 1 4) (sourceB1348 + difference 4 1) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1348 + difference 1 4) (sourceB1348 + difference 4 1) sourceC1348) = raw21377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21377; decide +kernel
    rw [ha]
    exact (canonical21377 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1348 + difference 1 5) (sourceB1348 + difference 5 1) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1348 + difference 1 5) (sourceB1348 + difference 5 1) sourceC1348) = raw11476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11476; decide +kernel
    rw [ha]
    exact (canonical11476 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1348 + difference 2 0) (sourceB1348 + difference 0 2) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4151) := by
    have ha : (tripleCharges (sourceA1348 + difference 2 0) (sourceB1348 + difference 0 2) sourceC1348) = raw21378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21378; decide +kernel
    rw [ha]
    exact (canonical21378 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1348 + difference 2 1) (sourceB1348 + difference 1 2) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA1348 + difference 2 1) (sourceB1348 + difference 1 2) sourceC1348) = raw21379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21379; decide +kernel
    rw [ha]
    exact (canonical21379 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1348 + difference 2 3) (sourceB1348 + difference 3 2) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4326) := by
    have ha : (tripleCharges (sourceA1348 + difference 2 3) (sourceB1348 + difference 3 2) sourceC1348) = raw21380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21380; decide +kernel
    rw [ha]
    exact (canonical21380 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1348 + difference 2 4) (sourceB1348 + difference 4 2) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1348 + difference 2 4) (sourceB1348 + difference 4 2) sourceC1348) = raw21381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21381; decide +kernel
    rw [ha]
    exact (canonical21381 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1348 + difference 2 5) (sourceB1348 + difference 5 2) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1348 + difference 2 5) (sourceB1348 + difference 5 2) sourceC1348) = raw11481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11481; decide +kernel
    rw [ha]
    exact (canonical11481 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1348 + difference 3 0) (sourceB1348 + difference 0 3) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4151) := by
    have ha : (tripleCharges (sourceA1348 + difference 3 0) (sourceB1348 + difference 0 3) sourceC1348) = raw21382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21382; decide +kernel
    rw [ha]
    exact (canonical21382 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1348 + difference 3 1) (sourceB1348 + difference 1 3) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA1348 + difference 3 1) (sourceB1348 + difference 1 3) sourceC1348) = raw21383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21383; decide +kernel
    rw [ha]
    exact (canonical21383 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1348 + difference 3 2) (sourceB1348 + difference 2 3) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4326) := by
    have ha : (tripleCharges (sourceA1348 + difference 3 2) (sourceB1348 + difference 2 3) sourceC1348) = raw21384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21384; decide +kernel
    rw [ha]
    exact (canonical21384 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1348 + difference 3 4) (sourceB1348 + difference 4 3) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1348 + difference 3 4) (sourceB1348 + difference 4 3) sourceC1348) = raw21385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21385; decide +kernel
    rw [ha]
    exact (canonical21385 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1348 + difference 3 5) (sourceB1348 + difference 5 3) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1348 + difference 3 5) (sourceB1348 + difference 5 3) sourceC1348) = raw11486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11486; decide +kernel
    rw [ha]
    exact (canonical11486 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1348 + difference 4 0) (sourceB1348 + difference 0 4) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4160) := by
    have ha : (tripleCharges (sourceA1348 + difference 4 0) (sourceB1348 + difference 0 4) sourceC1348) = raw21386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21386; decide +kernel
    rw [ha]
    exact (canonical21386 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1348 + difference 4 1) (sourceB1348 + difference 1 4) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4373) := by
    have ha : (tripleCharges (sourceA1348 + difference 4 1) (sourceB1348 + difference 1 4) sourceC1348) = raw21387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21387; decide +kernel
    rw [ha]
    exact (canonical21387 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1348 + difference 4 2) (sourceB1348 + difference 2 4) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA1348 + difference 4 2) (sourceB1348 + difference 2 4) sourceC1348) = raw21388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21388; decide +kernel
    rw [ha]
    exact (canonical21388 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1348 + difference 4 3) (sourceB1348 + difference 3 4) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA1348 + difference 4 3) (sourceB1348 + difference 3 4) sourceC1348) = raw21389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21389; decide +kernel
    rw [ha]
    exact (canonical21389 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1348 + difference 4 5) (sourceB1348 + difference 5 4) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1348 + difference 4 5) (sourceB1348 + difference 5 4) sourceC1348) = raw11491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11491; decide +kernel
    rw [ha]
    exact (canonical11491 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1348 + difference 5 0) (sourceB1348 + difference 0 5) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4156) := by
    have ha : (tripleCharges (sourceA1348 + difference 5 0) (sourceB1348 + difference 0 5) sourceC1348) = raw21390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21390; decide +kernel
    rw [ha]
    exact (canonical21390 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1348 + difference 5 1) (sourceB1348 + difference 1 5) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1348 + difference 5 1) (sourceB1348 + difference 1 5) sourceC1348) = raw21391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21391; decide +kernel
    rw [ha]
    exact (canonical21391 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1348 + difference 5 2) (sourceB1348 + difference 2 5) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1348 + difference 5 2) (sourceB1348 + difference 2 5) sourceC1348) = raw21392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21392; decide +kernel
    rw [ha]
    exact (canonical21392 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1348 + difference 5 3) (sourceB1348 + difference 3 5) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1348 + difference 5 3) (sourceB1348 + difference 3 5) sourceC1348) = raw21393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21393; decide +kernel
    rw [ha]
    exact (canonical21393 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1348 + difference 5 4) (sourceB1348 + difference 4 5) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1348 + difference 5 4) (sourceB1348 + difference 4 5) sourceC1348) = raw21394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21394; decide +kernel
    rw [ha]
    exact (canonical21394 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1348 sourceB1348 sourceC1348
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1348, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1349 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1349 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1349 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1349 : Integer.Sparse Master := [(Sum.inr 630, 2), (Sum.inr 633, 1), (Sum.inr 636, 1), (Sum.inr 647, 1), (Sum.inr 1118, 2), (Sum.inr 1142, 1), (Sum.inr 1275, 1), (Sum.inr 1320, 2), (Sum.inr 1325, 1), (Sum.inr 1329, 2), (Sum.inr 1334, 2), (Sum.inr 1342, 2), (Sum.inr 1414, 2), (Sum.inr 1416, 2), (Sum.inr 1419, 1), (Sum.inr 1448, 1), (Sum.inr 1450, 1), (Sum.inr 2941, 2), (Sum.inr 2966, 1), (Sum.inr 3114, 1), (Sum.inr 3230, 1)]

theorem sourceEq1349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1349 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1349 + difference 0 1) (sourceB1349 + difference 1 0) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA1349 + difference 0 1) (sourceB1349 + difference 1 0) sourceC1349) = raw21395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21395; decide +kernel
    rw [ha]
    exact (canonical21395 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1349 + difference 0 2) (sourceB1349 + difference 2 0) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA1349 + difference 0 2) (sourceB1349 + difference 2 0) sourceC1349) = raw21396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21396; decide +kernel
    rw [ha]
    exact (canonical21396 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1349 + difference 0 3) (sourceB1349 + difference 3 0) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA1349 + difference 0 3) (sourceB1349 + difference 3 0) sourceC1349) = raw21397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21397; decide +kernel
    rw [ha]
    exact (canonical21397 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1349 + difference 0 4) (sourceB1349 + difference 4 0) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA1349 + difference 0 4) (sourceB1349 + difference 4 0) sourceC1349) = raw21398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21398; decide +kernel
    rw [ha]
    exact (canonical21398 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1349 + difference 0 5) (sourceB1349 + difference 5 0) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA1349 + difference 0 5) (sourceB1349 + difference 5 0) sourceC1349) = raw21399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21399; decide +kernel
    rw [ha]
    exact (canonical21399 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1349 + difference 1 0) (sourceB1349 + difference 0 1) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 647) := by
    have ha : (tripleCharges (sourceA1349 + difference 1 0) (sourceB1349 + difference 0 1) sourceC1349) = raw21400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21400; decide +kernel
    rw [ha]
    exact (canonical21400 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1349 + difference 1 2) (sourceB1349 + difference 2 1) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1342) := by
    have ha : (tripleCharges (sourceA1349 + difference 1 2) (sourceB1349 + difference 2 1) sourceC1349) = raw21401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21401; decide +kernel
    rw [ha]
    exact (canonical21401 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1349 + difference 1 3) (sourceB1349 + difference 3 1) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1342) := by
    have ha : (tripleCharges (sourceA1349 + difference 1 3) (sourceB1349 + difference 3 1) sourceC1349) = raw21402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21402; decide +kernel
    rw [ha]
    exact (canonical21402 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1349 + difference 1 4) (sourceB1349 + difference 4 1) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1450) := by
    have ha : (tripleCharges (sourceA1349 + difference 1 4) (sourceB1349 + difference 4 1) sourceC1349) = raw21403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21403; decide +kernel
    rw [ha]
    exact (canonical21403 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1349 + difference 1 5) (sourceB1349 + difference 5 1) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1448) := by
    have ha : (tripleCharges (sourceA1349 + difference 1 5) (sourceB1349 + difference 5 1) sourceC1349) = raw21404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21404; decide +kernel
    rw [ha]
    exact (canonical21404 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1349 + difference 2 0) (sourceB1349 + difference 0 2) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 630) := by
    have ha : (tripleCharges (sourceA1349 + difference 2 0) (sourceB1349 + difference 0 2) sourceC1349) = raw21405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21405; decide +kernel
    rw [ha]
    exact (canonical21405 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1349 + difference 2 1) (sourceB1349 + difference 1 2) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1320) := by
    have ha : (tripleCharges (sourceA1349 + difference 2 1) (sourceB1349 + difference 1 2) sourceC1349) = raw21406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21406; decide +kernel
    rw [ha]
    exact (canonical21406 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1349 + difference 2 3) (sourceB1349 + difference 3 2) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1329) := by
    have ha : (tripleCharges (sourceA1349 + difference 2 3) (sourceB1349 + difference 3 2) sourceC1349) = raw21407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21407; decide +kernel
    rw [ha]
    exact (canonical21407 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1349 + difference 2 4) (sourceB1349 + difference 4 2) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1349 + difference 2 4) (sourceB1349 + difference 4 2) sourceC1349) = raw21408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21408; decide +kernel
    rw [ha]
    exact (canonical21408 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1349 + difference 2 5) (sourceB1349 + difference 5 2) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1349 + difference 2 5) (sourceB1349 + difference 5 2) sourceC1349) = raw21409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21409; decide +kernel
    rw [ha]
    exact (canonical21409 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1349 + difference 3 0) (sourceB1349 + difference 0 3) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 630) := by
    have ha : (tripleCharges (sourceA1349 + difference 3 0) (sourceB1349 + difference 0 3) sourceC1349) = raw21410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21410; decide +kernel
    rw [ha]
    exact (canonical21410 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1349 + difference 3 1) (sourceB1349 + difference 1 3) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1320) := by
    have ha : (tripleCharges (sourceA1349 + difference 3 1) (sourceB1349 + difference 1 3) sourceC1349) = raw21411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21411; decide +kernel
    rw [ha]
    exact (canonical21411 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1349 + difference 3 2) (sourceB1349 + difference 2 3) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1329) := by
    have ha : (tripleCharges (sourceA1349 + difference 3 2) (sourceB1349 + difference 2 3) sourceC1349) = raw21412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21412; decide +kernel
    rw [ha]
    exact (canonical21412 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1349 + difference 3 4) (sourceB1349 + difference 4 3) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1349 + difference 3 4) (sourceB1349 + difference 4 3) sourceC1349) = raw21413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21413; decide +kernel
    rw [ha]
    exact (canonical21413 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1349 + difference 3 5) (sourceB1349 + difference 5 3) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1349 + difference 3 5) (sourceB1349 + difference 5 3) sourceC1349) = raw21414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21414; decide +kernel
    rw [ha]
    exact (canonical21414 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1349 + difference 4 0) (sourceB1349 + difference 0 4) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 636) := by
    have ha : (tripleCharges (sourceA1349 + difference 4 0) (sourceB1349 + difference 0 4) sourceC1349) = raw21415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21415; decide +kernel
    rw [ha]
    exact (canonical21415 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1349 + difference 4 1) (sourceB1349 + difference 1 4) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1325) := by
    have ha : (tripleCharges (sourceA1349 + difference 4 1) (sourceB1349 + difference 1 4) sourceC1349) = raw21416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21416; decide +kernel
    rw [ha]
    exact (canonical21416 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1349 + difference 4 2) (sourceB1349 + difference 2 4) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1334) := by
    have ha : (tripleCharges (sourceA1349 + difference 4 2) (sourceB1349 + difference 2 4) sourceC1349) = raw21417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21417; decide +kernel
    rw [ha]
    exact (canonical21417 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1349 + difference 4 3) (sourceB1349 + difference 3 4) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1334) := by
    have ha : (tripleCharges (sourceA1349 + difference 4 3) (sourceB1349 + difference 3 4) sourceC1349) = raw21418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21418; decide +kernel
    rw [ha]
    exact (canonical21418 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1349 + difference 4 5) (sourceB1349 + difference 5 4) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1349 + difference 4 5) (sourceB1349 + difference 5 4) sourceC1349) = raw21419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21419; decide +kernel
    rw [ha]
    exact (canonical21419 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1349 + difference 5 0) (sourceB1349 + difference 0 5) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 633) := by
    have ha : (tripleCharges (sourceA1349 + difference 5 0) (sourceB1349 + difference 0 5) sourceC1349) = raw21420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21420; decide +kernel
    rw [ha]
    exact (canonical21420 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1349 + difference 5 1) (sourceB1349 + difference 1 5) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1349 + difference 5 1) (sourceB1349 + difference 1 5) sourceC1349) = raw21421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21421; decide +kernel
    rw [ha]
    exact (canonical21421 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1349 + difference 5 2) (sourceB1349 + difference 2 5) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1349 + difference 5 2) (sourceB1349 + difference 2 5) sourceC1349) = raw21422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21422; decide +kernel
    rw [ha]
    exact (canonical21422 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1349 + difference 5 3) (sourceB1349 + difference 3 5) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1349 + difference 5 3) (sourceB1349 + difference 3 5) sourceC1349) = raw21423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21423; decide +kernel
    rw [ha]
    exact (canonical21423 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1349 + difference 5 4) (sourceB1349 + difference 4 5) sourceC1349) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1349 + difference 5 4) (sourceB1349 + difference 4 5) sourceC1349) = raw21424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1349 sourceB1349 sourceC1349 difference raw21424; decide +kernel
    rw [ha]
    exact (canonical21424 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1349 sourceB1349 sourceC1349
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1349, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1350 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1350 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1350 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1350 : Integer.Sparse Master := [(Sum.inr 1505, 2), (Sum.inr 1516, 1), (Sum.inr 1518, 1), (Sum.inr 1523, 1), (Sum.inr 1663, 2), (Sum.inr 1672, 2), (Sum.inr 1674, 2), (Sum.inr 1679, 2), (Sum.inr 1704, 2), (Sum.inr 1707, 2), (Sum.inr 1722, 1), (Sum.inr 1725, 2), (Sum.inr 1727, 1), (Sum.inr 1735, 1), (Sum.inr 1738, 1), (Sum.inr 1752, 1), (Sum.inr 1754, 1), (Sum.inr 2203, 2), (Sum.inr 2261, 1), (Sum.inr 2264, 1), (Sum.inr 2292, 1)]

theorem sourceEq1350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1350 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1350 + difference 0 1) (sourceB1350 + difference 1 0) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1350 + difference 0 1) (sourceB1350 + difference 1 0) sourceC1350) = raw21425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21425; decide +kernel
    rw [ha]
    exact (canonical21425 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1350 + difference 0 2) (sourceB1350 + difference 2 0) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1350 + difference 0 2) (sourceB1350 + difference 2 0) sourceC1350) = raw21426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21426; decide +kernel
    rw [ha]
    exact (canonical21426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1350 + difference 0 3) (sourceB1350 + difference 3 0) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1350 + difference 0 3) (sourceB1350 + difference 3 0) sourceC1350) = raw21427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21427; decide +kernel
    rw [ha]
    exact (canonical21427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1350 + difference 0 4) (sourceB1350 + difference 4 0) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA1350 + difference 0 4) (sourceB1350 + difference 4 0) sourceC1350) = raw21428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21428; decide +kernel
    rw [ha]
    exact (canonical21428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1350 + difference 0 5) (sourceB1350 + difference 5 0) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA1350 + difference 0 5) (sourceB1350 + difference 5 0) sourceC1350) = raw21429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21429; decide +kernel
    rw [ha]
    exact (canonical21429 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1350 + difference 1 0) (sourceB1350 + difference 0 1) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA1350 + difference 1 0) (sourceB1350 + difference 0 1) sourceC1350) = raw21430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21430; decide +kernel
    rw [ha]
    exact (canonical21430 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1350 + difference 1 2) (sourceB1350 + difference 2 1) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1350 + difference 1 2) (sourceB1350 + difference 2 1) sourceC1350) = raw21431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21431; decide +kernel
    rw [ha]
    exact (canonical21431 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1350 + difference 1 3) (sourceB1350 + difference 3 1) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1350 + difference 1 3) (sourceB1350 + difference 3 1) sourceC1350) = raw21432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21432; decide +kernel
    rw [ha]
    exact (canonical21432 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1350 + difference 1 4) (sourceB1350 + difference 4 1) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1350 + difference 1 4) (sourceB1350 + difference 4 1) sourceC1350) = raw21433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21433; decide +kernel
    rw [ha]
    exact (canonical21433 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1350 + difference 1 5) (sourceB1350 + difference 5 1) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1350 + difference 1 5) (sourceB1350 + difference 5 1) sourceC1350) = raw21434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21434; decide +kernel
    rw [ha]
    exact (canonical21434 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1350 + difference 2 0) (sourceB1350 + difference 0 2) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA1350 + difference 2 0) (sourceB1350 + difference 0 2) sourceC1350) = raw21435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21435; decide +kernel
    rw [ha]
    exact (canonical21435 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1350 + difference 2 1) (sourceB1350 + difference 1 2) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA1350 + difference 2 1) (sourceB1350 + difference 1 2) sourceC1350) = raw21436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21436; decide +kernel
    rw [ha]
    exact (canonical21436 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1350 + difference 2 3) (sourceB1350 + difference 3 2) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1663) := by
    have ha : (tripleCharges (sourceA1350 + difference 2 3) (sourceB1350 + difference 3 2) sourceC1350) = raw21437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21437; decide +kernel
    rw [ha]
    exact (canonical21437 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1350 + difference 2 4) (sourceB1350 + difference 4 2) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1350 + difference 2 4) (sourceB1350 + difference 4 2) sourceC1350) = raw21438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21438; decide +kernel
    rw [ha]
    exact (canonical21438 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1350 + difference 2 5) (sourceB1350 + difference 5 2) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1350 + difference 2 5) (sourceB1350 + difference 5 2) sourceC1350) = raw21439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21439; decide +kernel
    rw [ha]
    exact (canonical21439 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1350 + difference 3 0) (sourceB1350 + difference 0 3) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA1350 + difference 3 0) (sourceB1350 + difference 0 3) sourceC1350) = raw21440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21440; decide +kernel
    rw [ha]
    exact (canonical21440 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1350 + difference 3 1) (sourceB1350 + difference 1 3) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA1350 + difference 3 1) (sourceB1350 + difference 1 3) sourceC1350) = raw21441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21441; decide +kernel
    rw [ha]
    exact (canonical21441 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1350 + difference 3 2) (sourceB1350 + difference 2 3) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1663) := by
    have ha : (tripleCharges (sourceA1350 + difference 3 2) (sourceB1350 + difference 2 3) sourceC1350) = raw21442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21442; decide +kernel
    rw [ha]
    exact (canonical21442 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1350 + difference 3 4) (sourceB1350 + difference 4 3) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1350 + difference 3 4) (sourceB1350 + difference 4 3) sourceC1350) = raw21443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21443; decide +kernel
    rw [ha]
    exact (canonical21443 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1350 + difference 3 5) (sourceB1350 + difference 5 3) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1350 + difference 3 5) (sourceB1350 + difference 5 3) sourceC1350) = raw21444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21444; decide +kernel
    rw [ha]
    exact (canonical21444 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1350 + difference 4 0) (sourceB1350 + difference 0 4) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA1350 + difference 4 0) (sourceB1350 + difference 0 4) sourceC1350) = raw21445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21445; decide +kernel
    rw [ha]
    exact (canonical21445 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1350 + difference 4 1) (sourceB1350 + difference 1 4) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA1350 + difference 4 1) (sourceB1350 + difference 1 4) sourceC1350) = raw21446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21446; decide +kernel
    rw [ha]
    exact (canonical21446 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1350 + difference 4 2) (sourceB1350 + difference 2 4) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA1350 + difference 4 2) (sourceB1350 + difference 2 4) sourceC1350) = raw21447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21447; decide +kernel
    rw [ha]
    exact (canonical21447 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1350 + difference 4 3) (sourceB1350 + difference 3 4) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA1350 + difference 4 3) (sourceB1350 + difference 3 4) sourceC1350) = raw21448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21448; decide +kernel
    rw [ha]
    exact (canonical21448 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1350 + difference 4 5) (sourceB1350 + difference 5 4) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1350 + difference 4 5) (sourceB1350 + difference 5 4) sourceC1350) = raw21449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21449; decide +kernel
    rw [ha]
    exact (canonical21449 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1350 + difference 5 0) (sourceB1350 + difference 0 5) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA1350 + difference 5 0) (sourceB1350 + difference 0 5) sourceC1350) = raw21450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21450; decide +kernel
    rw [ha]
    exact (canonical21450 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1350 + difference 5 1) (sourceB1350 + difference 1 5) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1350 + difference 5 1) (sourceB1350 + difference 1 5) sourceC1350) = raw21451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21451; decide +kernel
    rw [ha]
    exact (canonical21451 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1350 + difference 5 2) (sourceB1350 + difference 2 5) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1350 + difference 5 2) (sourceB1350 + difference 2 5) sourceC1350) = raw21452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21452; decide +kernel
    rw [ha]
    exact (canonical21452 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1350 + difference 5 3) (sourceB1350 + difference 3 5) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1350 + difference 5 3) (sourceB1350 + difference 3 5) sourceC1350) = raw21453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21453; decide +kernel
    rw [ha]
    exact (canonical21453 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1350 + difference 5 4) (sourceB1350 + difference 4 5) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1350 + difference 5 4) (sourceB1350 + difference 4 5) sourceC1350) = raw21454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21454; decide +kernel
    rw [ha]
    exact (canonical21454 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1350 sourceB1350 sourceC1350
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1350, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1351 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1351 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1351 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1351 : Integer.Sparse Master := [(Sum.inr 579, 2), (Sum.inr 584, 1), (Sum.inr 588, 1), (Sum.inr 605, 1), (Sum.inr 1043, 1), (Sum.inr 4084, -1)]

theorem sourceEq1351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1351 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1351 + difference 0 0) (sourceB1351 + difference 0 0) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1351 + difference 0 0) (sourceB1351 + difference 0 0) sourceC1351) = raw21455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21455; decide +kernel
    rw [ha]
    exact (canonical21455 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1351 + difference 1 0) (sourceB1351 + difference 0 1) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 605) := by
    have ha : (tripleCharges (sourceA1351 + difference 1 0) (sourceB1351 + difference 0 1) sourceC1351) = raw21456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21456; decide +kernel
    rw [ha]
    exact (canonical21456 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1351 + difference 2 0) (sourceB1351 + difference 0 2) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 579) := by
    have ha : (tripleCharges (sourceA1351 + difference 2 0) (sourceB1351 + difference 0 2) sourceC1351) = raw21457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21457; decide +kernel
    rw [ha]
    exact (canonical21457 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1351 + difference 3 0) (sourceB1351 + difference 0 3) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 579) := by
    have ha : (tripleCharges (sourceA1351 + difference 3 0) (sourceB1351 + difference 0 3) sourceC1351) = raw21458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21458; decide +kernel
    rw [ha]
    exact (canonical21458 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1351 + difference 4 0) (sourceB1351 + difference 0 4) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 588) := by
    have ha : (tripleCharges (sourceA1351 + difference 4 0) (sourceB1351 + difference 0 4) sourceC1351) = raw21459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21459; decide +kernel
    rw [ha]
    exact (canonical21459 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1351 + difference 5 0) (sourceB1351 + difference 0 5) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 584) := by
    have ha : (tripleCharges (sourceA1351 + difference 5 0) (sourceB1351 + difference 0 5) sourceC1351) = raw21460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21460; decide +kernel
    rw [ha]
    exact (canonical21460 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1351 + sourceB1351) sourceC1351) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1351 + sourceB1351) sourceC1351) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1351 sourceB1351 sourceC1351 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1351 sourceB1351 sourceC1351
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1351, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1352 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1352 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1352 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1352 : Integer.Sparse Master := [(Sum.inr 605, 1), (Sum.inr 924, 2), (Sum.inr 1043, 1), (Sum.inr 1082, 1), (Sum.inr 1089, 1), (Sum.inr 4084, -1)]

theorem sourceEq1352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1352 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 0) (sourceB1352 + difference 0 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 605) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 0) (sourceB1352 + difference 0 1) sourceC1352) = raw21456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21456; decide +kernel
    rw [ha]
    exact (canonical21456 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 1) (sourceB1352 + difference 1 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 1) (sourceB1352 + difference 1 1) sourceC1352) = raw21455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21455; decide +kernel
    rw [ha]
    exact (canonical21455 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 2) (sourceB1352 + difference 2 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 2) (sourceB1352 + difference 2 1) sourceC1352) = raw21462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21462; decide +kernel
    rw [ha]
    exact (canonical21462 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 3) (sourceB1352 + difference 3 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 3) (sourceB1352 + difference 3 1) sourceC1352) = raw21463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21463; decide +kernel
    rw [ha]
    exact (canonical21463 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 4) (sourceB1352 + difference 4 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1089) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 4) (sourceB1352 + difference 4 1) sourceC1352) = raw21464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21464; decide +kernel
    rw [ha]
    exact (canonical21464 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 5) (sourceB1352 + difference 5 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 5) (sourceB1352 + difference 5 1) sourceC1352) = raw21465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21465; decide +kernel
    rw [ha]
    exact (canonical21465 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1352 + sourceB1352) sourceC1352) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1352 + sourceB1352) sourceC1352) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1352 sourceB1352 sourceC1352 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1352 sourceB1352 sourceC1352
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1352, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1353 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1353 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1353 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1353 : Integer.Sparse Master := [(Sum.inr 943, 2), (Sum.inr 948, 1), (Sum.inr 952, 1), (Sum.inr 1043, 1), (Sum.inr 2109, 1), (Sum.inr 4084, -1)]

theorem sourceEq1353 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1353 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1353 + difference 0 1) (sourceB1353 + difference 1 0) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA1353 + difference 0 1) (sourceB1353 + difference 1 0) sourceC1353) = raw21466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21466; decide +kernel
    rw [ha]
    exact (canonical21466 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1353 + difference 1 1) (sourceB1353 + difference 1 1) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1353 + difference 1 1) (sourceB1353 + difference 1 1) sourceC1353) = raw21455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21455; decide +kernel
    rw [ha]
    exact (canonical21455 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1353 + difference 2 1) (sourceB1353 + difference 1 2) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 943) := by
    have ha : (tripleCharges (sourceA1353 + difference 2 1) (sourceB1353 + difference 1 2) sourceC1353) = raw21467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21467; decide +kernel
    rw [ha]
    exact (canonical21467 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1353 + difference 3 1) (sourceB1353 + difference 1 3) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 943) := by
    have ha : (tripleCharges (sourceA1353 + difference 3 1) (sourceB1353 + difference 1 3) sourceC1353) = raw21468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21468; decide +kernel
    rw [ha]
    exact (canonical21468 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1353 + difference 4 1) (sourceB1353 + difference 1 4) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 952) := by
    have ha : (tripleCharges (sourceA1353 + difference 4 1) (sourceB1353 + difference 1 4) sourceC1353) = raw21469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21469; decide +kernel
    rw [ha]
    exact (canonical21469 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1353 + difference 5 1) (sourceB1353 + difference 1 5) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1353 + difference 5 1) (sourceB1353 + difference 1 5) sourceC1353) = raw21470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21470; decide +kernel
    rw [ha]
    exact (canonical21470 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1353 + sourceB1353) sourceC1353) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1353 + sourceB1353) sourceC1353) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1353 sourceB1353 sourceC1353 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1353 sourceB1353 sourceC1353
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1353, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1354 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1354 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1354 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1354 : Integer.Sparse Master := [(Sum.inr 579, 1), (Sum.inr 904, 1), (Sum.inr 943, 1), (Sum.inr 1040, 1), (Sum.inr 1043, 2), (Sum.inr 4084, -1)]

theorem sourceEq1354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1354 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 0) (sourceB1354 + difference 0 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 579) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 0) (sourceB1354 + difference 0 2) sourceC1354) = raw21457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21457; decide +kernel
    rw [ha]
    exact (canonical21457 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 1) (sourceB1354 + difference 1 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 943) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 1) (sourceB1354 + difference 1 2) sourceC1354) = raw21467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21467; decide +kernel
    rw [ha]
    exact (canonical21467 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 2) (sourceB1354 + difference 2 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 2) (sourceB1354 + difference 2 2) sourceC1354) = raw21455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21455; decide +kernel
    rw [ha]
    exact (canonical21455 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 3) (sourceB1354 + difference 3 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 904) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 3) (sourceB1354 + difference 3 2) sourceC1354) = raw21471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21471; decide +kernel
    rw [ha]
    exact (canonical21471 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 4) (sourceB1354 + difference 4 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 4) (sourceB1354 + difference 4 2) sourceC1354) = raw21472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21472; decide +kernel
    rw [ha]
    exact (canonical21472 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 5) (sourceB1354 + difference 5 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 5) (sourceB1354 + difference 5 2) sourceC1354) = raw21473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21473; decide +kernel
    rw [ha]
    exact (canonical21473 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1354 + sourceB1354) sourceC1354) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1354 + sourceB1354) sourceC1354) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1354 sourceB1354 sourceC1354 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1354 sourceB1354 sourceC1354
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1354, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1355 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1355 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1355 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1355 : Integer.Sparse Master := [(Sum.inr 904, 1), (Sum.inr 908, 1), (Sum.inr 912, 1), (Sum.inr 924, 1), (Sum.inr 1043, 1), (Sum.inr 2022, 1), (Sum.inr 4084, -1)]

theorem sourceEq1355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1355 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1355 + difference 0 2) (sourceB1355 + difference 2 0) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA1355 + difference 0 2) (sourceB1355 + difference 2 0) sourceC1355) = raw21474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21474; decide +kernel
    rw [ha]
    exact (canonical21474 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1355 + difference 1 2) (sourceB1355 + difference 2 1) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1355 + difference 1 2) (sourceB1355 + difference 2 1) sourceC1355) = raw21462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21462; decide +kernel
    rw [ha]
    exact (canonical21462 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1355 + difference 2 2) (sourceB1355 + difference 2 2) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1355 + difference 2 2) (sourceB1355 + difference 2 2) sourceC1355) = raw21455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21455; decide +kernel
    rw [ha]
    exact (canonical21455 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1355 + difference 3 2) (sourceB1355 + difference 2 3) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 904) := by
    have ha : (tripleCharges (sourceA1355 + difference 3 2) (sourceB1355 + difference 2 3) sourceC1355) = raw21475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21475; decide +kernel
    rw [ha]
    exact (canonical21475 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1355 + difference 4 2) (sourceB1355 + difference 2 4) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 912) := by
    have ha : (tripleCharges (sourceA1355 + difference 4 2) (sourceB1355 + difference 2 4) sourceC1355) = raw21476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21476; decide +kernel
    rw [ha]
    exact (canonical21476 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1355 + difference 5 2) (sourceB1355 + difference 2 5) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1355 + difference 5 2) (sourceB1355 + difference 2 5) sourceC1355) = raw21477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21477; decide +kernel
    rw [ha]
    exact (canonical21477 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1355 + sourceB1355) sourceC1355) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1355 + sourceB1355) sourceC1355) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1355 sourceB1355 sourceC1355 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1355 sourceB1355 sourceC1355
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1355, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1356 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1356 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1356 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm1356 : Integer.Sparse Master := [(Sum.inr 4101, 2), (Sum.inr 4103, 1), (Sum.inr 4110, 1), (Sum.inr 4121, 1), (Sum.inr 4287, 2), (Sum.inr 4289, 2), (Sum.inr 4295, 2), (Sum.inr 4303, 2), (Sum.inr 4346, 2), (Sum.inr 4350, 1), (Sum.inr 4360, 1), (Sum.inr 4401, 2), (Sum.inr 4405, 1), (Sum.inr 4428, 1), (Sum.inr 4458, 2), (Sum.inr 4467, 1), (Sum.inr 4499, 1), (Sum.inr 5075, 2), (Sum.inr 5171, 1), (Sum.inr 5261, 1), (Sum.inr 5293, 1)]

theorem sourceEq1356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1356 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1356 + difference 0 1) (sourceB1356 + difference 1 0) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1356 + difference 0 1) (sourceB1356 + difference 1 0) sourceC1356) = raw4936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw4936; decide +kernel
    rw [ha]
    exact (canonical4936 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1356 + difference 0 2) (sourceB1356 + difference 2 0) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1356 + difference 0 2) (sourceB1356 + difference 2 0) sourceC1356) = raw4937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw4937; decide +kernel
    rw [ha]
    exact (canonical4937 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1356 + difference 0 3) (sourceB1356 + difference 3 0) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1356 + difference 0 3) (sourceB1356 + difference 3 0) sourceC1356) = raw4938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw4938; decide +kernel
    rw [ha]
    exact (canonical4938 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1356 + difference 0 4) (sourceB1356 + difference 4 0) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA1356 + difference 0 4) (sourceB1356 + difference 4 0) sourceC1356) = raw2776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw2776; decide +kernel
    rw [ha]
    exact (canonical2776 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1356 + difference 0 5) (sourceB1356 + difference 5 0) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1356 + difference 0 5) (sourceB1356 + difference 5 0) sourceC1356) = raw2771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw2771; decide +kernel
    rw [ha]
    exact (canonical2771 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1356 + difference 1 0) (sourceB1356 + difference 0 1) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4121) := by
    have ha : (tripleCharges (sourceA1356 + difference 1 0) (sourceB1356 + difference 0 1) sourceC1356) = raw21478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21478; decide +kernel
    rw [ha]
    exact (canonical21478 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1356 + difference 1 2) (sourceB1356 + difference 2 1) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4303) := by
    have ha : (tripleCharges (sourceA1356 + difference 1 2) (sourceB1356 + difference 2 1) sourceC1356) = raw21479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21479; decide +kernel
    rw [ha]
    exact (canonical21479 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1356 + difference 1 3) (sourceB1356 + difference 3 1) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4303) := by
    have ha : (tripleCharges (sourceA1356 + difference 1 3) (sourceB1356 + difference 3 1) sourceC1356) = raw21480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21480; decide +kernel
    rw [ha]
    exact (canonical21480 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1356 + difference 1 4) (sourceB1356 + difference 4 1) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1356 + difference 1 4) (sourceB1356 + difference 4 1) sourceC1356) = raw4923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw4923; decide +kernel
    rw [ha]
    exact (canonical4923 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1356 + difference 1 5) (sourceB1356 + difference 5 1) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1356 + difference 1 5) (sourceB1356 + difference 5 1) sourceC1356) = raw21481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21481; decide +kernel
    rw [ha]
    exact (canonical21481 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1356 + difference 2 0) (sourceB1356 + difference 0 2) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4101) := by
    have ha : (tripleCharges (sourceA1356 + difference 2 0) (sourceB1356 + difference 0 2) sourceC1356) = raw21482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21482; decide +kernel
    rw [ha]
    exact (canonical21482 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1356 + difference 2 1) (sourceB1356 + difference 1 2) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1356 + difference 2 1) (sourceB1356 + difference 1 2) sourceC1356) = raw21483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21483; decide +kernel
    rw [ha]
    exact (canonical21483 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1356 + difference 2 3) (sourceB1356 + difference 3 2) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4287) := by
    have ha : (tripleCharges (sourceA1356 + difference 2 3) (sourceB1356 + difference 3 2) sourceC1356) = raw21484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21484; decide +kernel
    rw [ha]
    exact (canonical21484 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1356 + difference 2 4) (sourceB1356 + difference 4 2) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1356 + difference 2 4) (sourceB1356 + difference 4 2) sourceC1356) = raw4927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw4927; decide +kernel
    rw [ha]
    exact (canonical4927 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1356 + difference 2 5) (sourceB1356 + difference 5 2) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1356 + difference 2 5) (sourceB1356 + difference 5 2) sourceC1356) = raw21485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21485; decide +kernel
    rw [ha]
    exact (canonical21485 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1356 + difference 3 0) (sourceB1356 + difference 0 3) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4101) := by
    have ha : (tripleCharges (sourceA1356 + difference 3 0) (sourceB1356 + difference 0 3) sourceC1356) = raw21486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21486; decide +kernel
    rw [ha]
    exact (canonical21486 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1356 + difference 3 1) (sourceB1356 + difference 1 3) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1356 + difference 3 1) (sourceB1356 + difference 1 3) sourceC1356) = raw21487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21487; decide +kernel
    rw [ha]
    exact (canonical21487 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1356 + difference 3 2) (sourceB1356 + difference 2 3) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4287) := by
    have ha : (tripleCharges (sourceA1356 + difference 3 2) (sourceB1356 + difference 2 3) sourceC1356) = raw21488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21488; decide +kernel
    rw [ha]
    exact (canonical21488 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1356 + difference 3 4) (sourceB1356 + difference 4 3) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1356 + difference 3 4) (sourceB1356 + difference 4 3) sourceC1356) = raw4931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw4931; decide +kernel
    rw [ha]
    exact (canonical4931 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1356 + difference 3 5) (sourceB1356 + difference 5 3) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1356 + difference 3 5) (sourceB1356 + difference 5 3) sourceC1356) = raw21489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21489; decide +kernel
    rw [ha]
    exact (canonical21489 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1356 + difference 4 0) (sourceB1356 + difference 0 4) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4110) := by
    have ha : (tripleCharges (sourceA1356 + difference 4 0) (sourceB1356 + difference 0 4) sourceC1356) = raw21490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21490; decide +kernel
    rw [ha]
    exact (canonical21490 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1356 + difference 4 1) (sourceB1356 + difference 1 4) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1356 + difference 4 1) (sourceB1356 + difference 1 4) sourceC1356) = raw21491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21491; decide +kernel
    rw [ha]
    exact (canonical21491 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1356 + difference 4 2) (sourceB1356 + difference 2 4) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA1356 + difference 4 2) (sourceB1356 + difference 2 4) sourceC1356) = raw21492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21492; decide +kernel
    rw [ha]
    exact (canonical21492 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1356 + difference 4 3) (sourceB1356 + difference 3 4) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA1356 + difference 4 3) (sourceB1356 + difference 3 4) sourceC1356) = raw21493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21493; decide +kernel
    rw [ha]
    exact (canonical21493 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1356 + difference 4 5) (sourceB1356 + difference 5 4) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1356 + difference 4 5) (sourceB1356 + difference 5 4) sourceC1356) = raw21494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21494; decide +kernel
    rw [ha]
    exact (canonical21494 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1356 + difference 5 0) (sourceB1356 + difference 0 5) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4103) := by
    have ha : (tripleCharges (sourceA1356 + difference 5 0) (sourceB1356 + difference 0 5) sourceC1356) = raw21495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21495; decide +kernel
    rw [ha]
    exact (canonical21495 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1356 + difference 5 1) (sourceB1356 + difference 1 5) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1356 + difference 5 1) (sourceB1356 + difference 1 5) sourceC1356) = raw21496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21496; decide +kernel
    rw [ha]
    exact (canonical21496 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1356 + difference 5 2) (sourceB1356 + difference 2 5) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4289) := by
    have ha : (tripleCharges (sourceA1356 + difference 5 2) (sourceB1356 + difference 2 5) sourceC1356) = raw21497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21497; decide +kernel
    rw [ha]
    exact (canonical21497 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1356 + difference 5 3) (sourceB1356 + difference 3 5) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4289) := by
    have ha : (tripleCharges (sourceA1356 + difference 5 3) (sourceB1356 + difference 3 5) sourceC1356) = raw21498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw21498; decide +kernel
    rw [ha]
    exact (canonical21498 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1356 + difference 5 4) (sourceB1356 + difference 4 5) sourceC1356) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1356 + difference 5 4) (sourceB1356 + difference 4 5) sourceC1356) = raw4939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1356 sourceB1356 sourceC1356 difference raw4939; decide +kernel
    rw [ha]
    exact (canonical4939 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1356 sourceB1356 sourceC1356
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1356, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1357 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1357 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1357 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm1357 : Integer.Sparse Master := [(Sum.inr 538, 2), (Sum.inr 540, 1), (Sum.inr 547, 1), (Sum.inr 555, 1), (Sum.inr 865, 2), (Sum.inr 867, 2), (Sum.inr 873, 2), (Sum.inr 881, 2), (Sum.inr 924, 2), (Sum.inr 928, 1), (Sum.inr 938, 1), (Sum.inr 982, 2), (Sum.inr 986, 1), (Sum.inr 1009, 1), (Sum.inr 1041, 2), (Sum.inr 1050, 1), (Sum.inr 1083, 1), (Sum.inr 2482, 2), (Sum.inr 2598, 1), (Sum.inr 2726, 1), (Sum.inr 2767, 1)]

theorem sourceEq1357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1357 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1357 + difference 0 1) (sourceB1357 + difference 1 0) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2598) := by
    have ha : (tripleCharges (sourceA1357 + difference 0 1) (sourceB1357 + difference 1 0) sourceC1357) = raw4958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw4958; decide +kernel
    rw [ha]
    exact (canonical4958 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1357 + difference 0 2) (sourceB1357 + difference 2 0) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1357 + difference 0 2) (sourceB1357 + difference 2 0) sourceC1357) = raw4959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw4959; decide +kernel
    rw [ha]
    exact (canonical4959 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1357 + difference 0 3) (sourceB1357 + difference 3 0) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1357 + difference 0 3) (sourceB1357 + difference 3 0) sourceC1357) = raw4960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw4960; decide +kernel
    rw [ha]
    exact (canonical4960 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1357 + difference 0 4) (sourceB1357 + difference 4 0) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA1357 + difference 0 4) (sourceB1357 + difference 4 0) sourceC1357) = raw2806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw2806; decide +kernel
    rw [ha]
    exact (canonical2806 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1357 + difference 0 5) (sourceB1357 + difference 5 0) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA1357 + difference 0 5) (sourceB1357 + difference 5 0) sourceC1357) = raw2801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw2801; decide +kernel
    rw [ha]
    exact (canonical2801 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1357 + difference 1 0) (sourceB1357 + difference 0 1) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 555) := by
    have ha : (tripleCharges (sourceA1357 + difference 1 0) (sourceB1357 + difference 0 1) sourceC1357) = raw21499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21499; decide +kernel
    rw [ha]
    exact (canonical21499 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1357 + difference 1 2) (sourceB1357 + difference 2 1) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 881) := by
    have ha : (tripleCharges (sourceA1357 + difference 1 2) (sourceB1357 + difference 2 1) sourceC1357) = raw21500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21500; decide +kernel
    rw [ha]
    exact (canonical21500 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1357 + difference 1 3) (sourceB1357 + difference 3 1) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 881) := by
    have ha : (tripleCharges (sourceA1357 + difference 1 3) (sourceB1357 + difference 3 1) sourceC1357) = raw21501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21501; decide +kernel
    rw [ha]
    exact (canonical21501 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1357 + difference 1 4) (sourceB1357 + difference 4 1) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1357 + difference 1 4) (sourceB1357 + difference 4 1) sourceC1357) = raw4945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw4945; decide +kernel
    rw [ha]
    exact (canonical4945 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1357 + difference 1 5) (sourceB1357 + difference 5 1) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1357 + difference 1 5) (sourceB1357 + difference 5 1) sourceC1357) = raw21502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21502; decide +kernel
    rw [ha]
    exact (canonical21502 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1357 + difference 2 0) (sourceB1357 + difference 0 2) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 538) := by
    have ha : (tripleCharges (sourceA1357 + difference 2 0) (sourceB1357 + difference 0 2) sourceC1357) = raw21503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21503; decide +kernel
    rw [ha]
    exact (canonical21503 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1357 + difference 2 1) (sourceB1357 + difference 1 2) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1357 + difference 2 1) (sourceB1357 + difference 1 2) sourceC1357) = raw21504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21504; decide +kernel
    rw [ha]
    exact (canonical21504 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1357 + difference 2 3) (sourceB1357 + difference 3 2) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 865) := by
    have ha : (tripleCharges (sourceA1357 + difference 2 3) (sourceB1357 + difference 3 2) sourceC1357) = raw21505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21505; decide +kernel
    rw [ha]
    exact (canonical21505 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1357 + difference 2 4) (sourceB1357 + difference 4 2) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1357 + difference 2 4) (sourceB1357 + difference 4 2) sourceC1357) = raw4949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw4949; decide +kernel
    rw [ha]
    exact (canonical4949 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1357 + difference 2 5) (sourceB1357 + difference 5 2) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1357 + difference 2 5) (sourceB1357 + difference 5 2) sourceC1357) = raw21506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21506; decide +kernel
    rw [ha]
    exact (canonical21506 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1357 + difference 3 0) (sourceB1357 + difference 0 3) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 538) := by
    have ha : (tripleCharges (sourceA1357 + difference 3 0) (sourceB1357 + difference 0 3) sourceC1357) = raw21507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21507; decide +kernel
    rw [ha]
    exact (canonical21507 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1357 + difference 3 1) (sourceB1357 + difference 1 3) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1357 + difference 3 1) (sourceB1357 + difference 1 3) sourceC1357) = raw21508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21508; decide +kernel
    rw [ha]
    exact (canonical21508 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1357 + difference 3 2) (sourceB1357 + difference 2 3) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 865) := by
    have ha : (tripleCharges (sourceA1357 + difference 3 2) (sourceB1357 + difference 2 3) sourceC1357) = raw21509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21509; decide +kernel
    rw [ha]
    exact (canonical21509 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1357 + difference 3 4) (sourceB1357 + difference 4 3) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1357 + difference 3 4) (sourceB1357 + difference 4 3) sourceC1357) = raw4953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw4953; decide +kernel
    rw [ha]
    exact (canonical4953 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1357 + difference 3 5) (sourceB1357 + difference 5 3) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1357 + difference 3 5) (sourceB1357 + difference 5 3) sourceC1357) = raw21510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21510; decide +kernel
    rw [ha]
    exact (canonical21510 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1357 + difference 4 0) (sourceB1357 + difference 0 4) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 547) := by
    have ha : (tripleCharges (sourceA1357 + difference 4 0) (sourceB1357 + difference 0 4) sourceC1357) = raw21511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21511; decide +kernel
    rw [ha]
    exact (canonical21511 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1357 + difference 4 1) (sourceB1357 + difference 1 4) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 938) := by
    have ha : (tripleCharges (sourceA1357 + difference 4 1) (sourceB1357 + difference 1 4) sourceC1357) = raw21512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21512; decide +kernel
    rw [ha]
    exact (canonical21512 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1357 + difference 4 2) (sourceB1357 + difference 2 4) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA1357 + difference 4 2) (sourceB1357 + difference 2 4) sourceC1357) = raw21513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21513; decide +kernel
    rw [ha]
    exact (canonical21513 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1357 + difference 4 3) (sourceB1357 + difference 3 4) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA1357 + difference 4 3) (sourceB1357 + difference 3 4) sourceC1357) = raw21514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21514; decide +kernel
    rw [ha]
    exact (canonical21514 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1357 + difference 4 5) (sourceB1357 + difference 5 4) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1357 + difference 4 5) (sourceB1357 + difference 5 4) sourceC1357) = raw21515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21515; decide +kernel
    rw [ha]
    exact (canonical21515 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1357 + difference 5 0) (sourceB1357 + difference 0 5) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 540) := by
    have ha : (tripleCharges (sourceA1357 + difference 5 0) (sourceB1357 + difference 0 5) sourceC1357) = raw21516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21516; decide +kernel
    rw [ha]
    exact (canonical21516 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1357 + difference 5 1) (sourceB1357 + difference 1 5) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 928) := by
    have ha : (tripleCharges (sourceA1357 + difference 5 1) (sourceB1357 + difference 1 5) sourceC1357) = raw21517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21517; decide +kernel
    rw [ha]
    exact (canonical21517 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1357 + difference 5 2) (sourceB1357 + difference 2 5) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 867) := by
    have ha : (tripleCharges (sourceA1357 + difference 5 2) (sourceB1357 + difference 2 5) sourceC1357) = raw21518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21518; decide +kernel
    rw [ha]
    exact (canonical21518 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1357 + difference 5 3) (sourceB1357 + difference 3 5) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 867) := by
    have ha : (tripleCharges (sourceA1357 + difference 5 3) (sourceB1357 + difference 3 5) sourceC1357) = raw21519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw21519; decide +kernel
    rw [ha]
    exact (canonical21519 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1357 + difference 5 4) (sourceB1357 + difference 4 5) sourceC1357) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 986) := by
    have ha : (tripleCharges (sourceA1357 + difference 5 4) (sourceB1357 + difference 4 5) sourceC1357) = raw4961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1357 sourceB1357 sourceC1357 difference raw4961; decide +kernel
    rw [ha]
    exact (canonical4961 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1357 sourceB1357 sourceC1357
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1357, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1358 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1358 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1358 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1358 : Integer.Sparse Master := [(Sum.inr 4251, 2), (Sum.inr 4266, 1), (Sum.inr 4269, 1), (Sum.inr 4272, 1), (Sum.inr 4390, 2), (Sum.inr 4398, 2), (Sum.inr 4401, 2), (Sum.inr 4408, 2), (Sum.inr 4437, 2), (Sum.inr 4440, 2), (Sum.inr 4454, 1), (Sum.inr 4460, 2), (Sum.inr 4463, 1), (Sum.inr 4472, 1), (Sum.inr 4476, 1), (Sum.inr 4501, 1), (Sum.inr 4505, 1), (Sum.inr 4591, 2), (Sum.inr 4608, 1), (Sum.inr 4609, 1), (Sum.inr 4625, 1)]

theorem sourceEq1358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1358 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1358 + difference 0 1) (sourceB1358 + difference 1 0) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1358 + difference 0 1) (sourceB1358 + difference 1 0) sourceC1358) = raw20584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20584; decide +kernel
    rw [ha]
    exact (canonical20584 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1358 + difference 0 2) (sourceB1358 + difference 2 0) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1358 + difference 0 2) (sourceB1358 + difference 2 0) sourceC1358) = raw20420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20420; decide +kernel
    rw [ha]
    exact (canonical20420 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1358 + difference 0 3) (sourceB1358 + difference 3 0) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1358 + difference 0 3) (sourceB1358 + difference 3 0) sourceC1358) = raw20421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20421; decide +kernel
    rw [ha]
    exact (canonical20421 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1358 + difference 0 4) (sourceB1358 + difference 4 0) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1358 + difference 0 4) (sourceB1358 + difference 4 0) sourceC1358) = raw20422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20422; decide +kernel
    rw [ha]
    exact (canonical20422 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1358 + difference 0 5) (sourceB1358 + difference 5 0) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1358 + difference 0 5) (sourceB1358 + difference 5 0) sourceC1358) = raw20423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20423; decide +kernel
    rw [ha]
    exact (canonical20423 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1358 + difference 1 0) (sourceB1358 + difference 0 1) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1358 + difference 1 0) (sourceB1358 + difference 0 1) sourceC1358) = raw21520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21520; decide +kernel
    rw [ha]
    exact (canonical21520 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1358 + difference 1 2) (sourceB1358 + difference 2 1) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4408) := by
    have ha : (tripleCharges (sourceA1358 + difference 1 2) (sourceB1358 + difference 2 1) sourceC1358) = raw21521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21521; decide +kernel
    rw [ha]
    exact (canonical21521 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1358 + difference 1 3) (sourceB1358 + difference 3 1) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4408) := by
    have ha : (tripleCharges (sourceA1358 + difference 1 3) (sourceB1358 + difference 3 1) sourceC1358) = raw21522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21522; decide +kernel
    rw [ha]
    exact (canonical21522 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1358 + difference 1 4) (sourceB1358 + difference 4 1) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4472) := by
    have ha : (tripleCharges (sourceA1358 + difference 1 4) (sourceB1358 + difference 4 1) sourceC1358) = raw21523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21523; decide +kernel
    rw [ha]
    exact (canonical21523 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1358 + difference 1 5) (sourceB1358 + difference 5 1) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA1358 + difference 1 5) (sourceB1358 + difference 5 1) sourceC1358) = raw21296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21296; decide +kernel
    rw [ha]
    exact (canonical21296 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1358 + difference 2 0) (sourceB1358 + difference 0 2) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1358 + difference 2 0) (sourceB1358 + difference 0 2) sourceC1358) = raw21524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21524; decide +kernel
    rw [ha]
    exact (canonical21524 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1358 + difference 2 1) (sourceB1358 + difference 1 2) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1358 + difference 2 1) (sourceB1358 + difference 1 2) sourceC1358) = raw20424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20424; decide +kernel
    rw [ha]
    exact (canonical20424 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1358 + difference 2 3) (sourceB1358 + difference 3 2) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4390) := by
    have ha : (tripleCharges (sourceA1358 + difference 2 3) (sourceB1358 + difference 3 2) sourceC1358) = raw21525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21525; decide +kernel
    rw [ha]
    exact (canonical21525 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1358 + difference 2 4) (sourceB1358 + difference 4 2) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4437) := by
    have ha : (tripleCharges (sourceA1358 + difference 2 4) (sourceB1358 + difference 4 2) sourceC1358) = raw21526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21526; decide +kernel
    rw [ha]
    exact (canonical21526 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1358 + difference 2 5) (sourceB1358 + difference 5 2) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1358 + difference 2 5) (sourceB1358 + difference 5 2) sourceC1358) = raw21301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21301; decide +kernel
    rw [ha]
    exact (canonical21301 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1358 + difference 3 0) (sourceB1358 + difference 0 3) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1358 + difference 3 0) (sourceB1358 + difference 0 3) sourceC1358) = raw21527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21527; decide +kernel
    rw [ha]
    exact (canonical21527 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1358 + difference 3 1) (sourceB1358 + difference 1 3) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1358 + difference 3 1) (sourceB1358 + difference 1 3) sourceC1358) = raw20429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20429; decide +kernel
    rw [ha]
    exact (canonical20429 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1358 + difference 3 2) (sourceB1358 + difference 2 3) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4390) := by
    have ha : (tripleCharges (sourceA1358 + difference 3 2) (sourceB1358 + difference 2 3) sourceC1358) = raw21528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21528; decide +kernel
    rw [ha]
    exact (canonical21528 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1358 + difference 3 4) (sourceB1358 + difference 4 3) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4437) := by
    have ha : (tripleCharges (sourceA1358 + difference 3 4) (sourceB1358 + difference 4 3) sourceC1358) = raw21529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21529; decide +kernel
    rw [ha]
    exact (canonical21529 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1358 + difference 3 5) (sourceB1358 + difference 5 3) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1358 + difference 3 5) (sourceB1358 + difference 5 3) sourceC1358) = raw21306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21306; decide +kernel
    rw [ha]
    exact (canonical21306 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1358 + difference 4 0) (sourceB1358 + difference 0 4) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1358 + difference 4 0) (sourceB1358 + difference 0 4) sourceC1358) = raw21313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21313; decide +kernel
    rw [ha]
    exact (canonical21313 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1358 + difference 4 1) (sourceB1358 + difference 1 4) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1358 + difference 4 1) (sourceB1358 + difference 1 4) sourceC1358) = raw20434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20434; decide +kernel
    rw [ha]
    exact (canonical20434 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1358 + difference 4 2) (sourceB1358 + difference 2 4) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1358 + difference 4 2) (sourceB1358 + difference 2 4) sourceC1358) = raw21314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21314; decide +kernel
    rw [ha]
    exact (canonical21314 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1358 + difference 4 3) (sourceB1358 + difference 3 4) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1358 + difference 4 3) (sourceB1358 + difference 3 4) sourceC1358) = raw20795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20795; decide +kernel
    rw [ha]
    exact (canonical20795 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1358 + difference 4 5) (sourceB1358 + difference 5 4) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1358 + difference 4 5) (sourceB1358 + difference 5 4) sourceC1358) = raw21530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21530; decide +kernel
    rw [ha]
    exact (canonical21530 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1358 + difference 5 0) (sourceB1358 + difference 0 5) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4266) := by
    have ha : (tripleCharges (sourceA1358 + difference 5 0) (sourceB1358 + difference 0 5) sourceC1358) = raw21531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21531; decide +kernel
    rw [ha]
    exact (canonical21531 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1358 + difference 5 1) (sourceB1358 + difference 1 5) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1358 + difference 5 1) (sourceB1358 + difference 1 5) sourceC1358) = raw20439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20439; decide +kernel
    rw [ha]
    exact (canonical20439 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1358 + difference 5 2) (sourceB1358 + difference 2 5) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1358 + difference 5 2) (sourceB1358 + difference 2 5) sourceC1358) = raw21532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw21532; decide +kernel
    rw [ha]
    exact (canonical21532 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1358 + difference 5 3) (sourceB1358 + difference 3 5) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1358 + difference 5 3) (sourceB1358 + difference 3 5) sourceC1358) = raw20967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20967; decide +kernel
    rw [ha]
    exact (canonical20967 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1358 + difference 5 4) (sourceB1358 + difference 4 5) sourceC1358) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA1358 + difference 5 4) (sourceB1358 + difference 4 5) sourceC1358) = raw20572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1358 sourceB1358 sourceC1358 difference raw20572; decide +kernel
    rw [ha]
    exact (canonical20572 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1358 sourceB1358 sourceC1358
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1358, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1359 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1359 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1359 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1359 : Integer.Sparse Master := [(Sum.inr 785, 2), (Sum.inr 809, 1), (Sum.inr 812, 1), (Sum.inr 826, 1), (Sum.inr 971, 2), (Sum.inr 979, 2), (Sum.inr 982, 2), (Sum.inr 989, 2), (Sum.inr 1019, 2), (Sum.inr 1022, 2), (Sum.inr 1037, 1), (Sum.inr 1043, 2), (Sum.inr 1046, 1), (Sum.inr 1055, 1), (Sum.inr 1059, 1), (Sum.inr 1085, 1), (Sum.inr 1089, 1), (Sum.inr 1215, 2), (Sum.inr 1264, 1), (Sum.inr 1269, 1), (Sum.inr 1304, 1)]

theorem sourceEq1359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1359 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1359 + difference 0 1) (sourceB1359 + difference 1 0) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA1359 + difference 0 1) (sourceB1359 + difference 1 0) sourceC1359) = raw20614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw20614; decide +kernel
    rw [ha]
    exact (canonical20614 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1359 + difference 0 2) (sourceB1359 + difference 2 0) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1359 + difference 0 2) (sourceB1359 + difference 2 0) sourceC1359) = raw21533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21533; decide +kernel
    rw [ha]
    exact (canonical21533 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1359 + difference 0 3) (sourceB1359 + difference 3 0) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1359 + difference 0 3) (sourceB1359 + difference 3 0) sourceC1359) = raw20820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw20820; decide +kernel
    rw [ha]
    exact (canonical20820 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1359 + difference 0 4) (sourceB1359 + difference 4 0) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA1359 + difference 0 4) (sourceB1359 + difference 4 0) sourceC1359) = raw20599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw20599; decide +kernel
    rw [ha]
    exact (canonical20599 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1359 + difference 0 5) (sourceB1359 + difference 5 0) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1269) := by
    have ha : (tripleCharges (sourceA1359 + difference 0 5) (sourceB1359 + difference 5 0) sourceC1359) = raw21316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21316; decide +kernel
    rw [ha]
    exact (canonical21316 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1359 + difference 1 0) (sourceB1359 + difference 0 1) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1359 + difference 1 0) (sourceB1359 + difference 0 1) sourceC1359) = raw21534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21534; decide +kernel
    rw [ha]
    exact (canonical21534 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1359 + difference 1 2) (sourceB1359 + difference 2 1) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA1359 + difference 1 2) (sourceB1359 + difference 2 1) sourceC1359) = raw21535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21535; decide +kernel
    rw [ha]
    exact (canonical21535 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1359 + difference 1 3) (sourceB1359 + difference 3 1) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA1359 + difference 1 3) (sourceB1359 + difference 3 1) sourceC1359) = raw21536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21536; decide +kernel
    rw [ha]
    exact (canonical21536 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1359 + difference 1 4) (sourceB1359 + difference 4 1) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1055) := by
    have ha : (tripleCharges (sourceA1359 + difference 1 4) (sourceB1359 + difference 4 1) sourceC1359) = raw21537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21537; decide +kernel
    rw [ha]
    exact (canonical21537 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1359 + difference 1 5) (sourceB1359 + difference 5 1) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA1359 + difference 1 5) (sourceB1359 + difference 5 1) sourceC1359) = raw21321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21321; decide +kernel
    rw [ha]
    exact (canonical21321 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1359 + difference 2 0) (sourceB1359 + difference 0 2) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1359 + difference 2 0) (sourceB1359 + difference 0 2) sourceC1359) = raw21538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21538; decide +kernel
    rw [ha]
    exact (canonical21538 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1359 + difference 2 1) (sourceB1359 + difference 1 2) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1359 + difference 2 1) (sourceB1359 + difference 1 2) sourceC1359) = raw21539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21539; decide +kernel
    rw [ha]
    exact (canonical21539 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1359 + difference 2 3) (sourceB1359 + difference 3 2) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 971) := by
    have ha : (tripleCharges (sourceA1359 + difference 2 3) (sourceB1359 + difference 3 2) sourceC1359) = raw21540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21540; decide +kernel
    rw [ha]
    exact (canonical21540 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1359 + difference 2 4) (sourceB1359 + difference 4 2) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1019) := by
    have ha : (tripleCharges (sourceA1359 + difference 2 4) (sourceB1359 + difference 4 2) sourceC1359) = raw21541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21541; decide +kernel
    rw [ha]
    exact (canonical21541 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1359 + difference 2 5) (sourceB1359 + difference 5 2) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA1359 + difference 2 5) (sourceB1359 + difference 5 2) sourceC1359) = raw21326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21326; decide +kernel
    rw [ha]
    exact (canonical21326 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1359 + difference 3 0) (sourceB1359 + difference 0 3) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1359 + difference 3 0) (sourceB1359 + difference 0 3) sourceC1359) = raw21542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21542; decide +kernel
    rw [ha]
    exact (canonical21542 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1359 + difference 3 1) (sourceB1359 + difference 1 3) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1359 + difference 3 1) (sourceB1359 + difference 1 3) sourceC1359) = raw21543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21543; decide +kernel
    rw [ha]
    exact (canonical21543 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1359 + difference 3 2) (sourceB1359 + difference 2 3) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 971) := by
    have ha : (tripleCharges (sourceA1359 + difference 3 2) (sourceB1359 + difference 2 3) sourceC1359) = raw21544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21544; decide +kernel
    rw [ha]
    exact (canonical21544 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1359 + difference 3 4) (sourceB1359 + difference 4 3) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1019) := by
    have ha : (tripleCharges (sourceA1359 + difference 3 4) (sourceB1359 + difference 4 3) sourceC1359) = raw21545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21545; decide +kernel
    rw [ha]
    exact (canonical21545 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1359 + difference 3 5) (sourceB1359 + difference 5 3) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA1359 + difference 3 5) (sourceB1359 + difference 5 3) sourceC1359) = raw21331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21331; decide +kernel
    rw [ha]
    exact (canonical21331 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1359 + difference 4 0) (sourceB1359 + difference 0 4) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1359 + difference 4 0) (sourceB1359 + difference 0 4) sourceC1359) = raw21338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21338; decide +kernel
    rw [ha]
    exact (canonical21338 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1359 + difference 4 1) (sourceB1359 + difference 1 4) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1089) := by
    have ha : (tripleCharges (sourceA1359 + difference 4 1) (sourceB1359 + difference 1 4) sourceC1359) = raw20827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw20827; decide +kernel
    rw [ha]
    exact (canonical20827 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1359 + difference 4 2) (sourceB1359 + difference 2 4) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1359 + difference 4 2) (sourceB1359 + difference 2 4) sourceC1359) = raw21339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21339; decide +kernel
    rw [ha]
    exact (canonical21339 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1359 + difference 4 3) (sourceB1359 + difference 3 4) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1359 + difference 4 3) (sourceB1359 + difference 3 4) sourceC1359) = raw20817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw20817; decide +kernel
    rw [ha]
    exact (canonical20817 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1359 + difference 4 5) (sourceB1359 + difference 5 4) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1359 + difference 4 5) (sourceB1359 + difference 5 4) sourceC1359) = raw21546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21546; decide +kernel
    rw [ha]
    exact (canonical21546 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1359 + difference 5 0) (sourceB1359 + difference 0 5) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1359 + difference 5 0) (sourceB1359 + difference 0 5) sourceC1359) = raw21547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21547; decide +kernel
    rw [ha]
    exact (canonical21547 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1359 + difference 5 1) (sourceB1359 + difference 1 5) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1085) := by
    have ha : (tripleCharges (sourceA1359 + difference 5 1) (sourceB1359 + difference 1 5) sourceC1359) = raw20610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw20610; decide +kernel
    rw [ha]
    exact (canonical20610 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1359 + difference 5 2) (sourceB1359 + difference 2 5) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1359 + difference 5 2) (sourceB1359 + difference 2 5) sourceC1359) = raw21548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21548; decide +kernel
    rw [ha]
    exact (canonical21548 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1359 + difference 5 3) (sourceB1359 + difference 3 5) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1359 + difference 5 3) (sourceB1359 + difference 3 5) sourceC1359) = raw21549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw21549; decide +kernel
    rw [ha]
    exact (canonical21549 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1359 + difference 5 4) (sourceB1359 + difference 4 5) sourceC1359) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1359 + difference 5 4) (sourceB1359 + difference 4 5) sourceC1359) = raw20595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1359 sourceB1359 sourceC1359 difference raw20595; decide +kernel
    rw [ha]
    exact (canonical20595 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1359 sourceB1359 sourceC1359
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1359, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1360 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1360 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1360 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1360 : Integer.Sparse Master := [(Sum.inr 1217, 2), (Sum.inr 1242, 1), (Sum.inr 1243, 1), (Sum.inr 1307, 1), (Sum.inr 1361, 2), (Sum.inr 1372, 1), (Sum.inr 1373, 1), (Sum.inr 1379, 2), (Sum.inr 1388, 2), (Sum.inr 1389, 2), (Sum.inr 1397, 2), (Sum.inr 1399, 2), (Sum.inr 1413, 1), (Sum.inr 1416, 2), (Sum.inr 1417, 1), (Sum.inr 1450, 1), (Sum.inr 1452, 1), (Sum.inr 1471, 1), (Sum.inr 1478, 2), (Sum.inr 1484, 1), (Sum.inr 1485, 1)]

theorem sourceEq1360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1360 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1360 + difference 0 1) (sourceB1360 + difference 1 0) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1360 + difference 0 1) (sourceB1360 + difference 1 0) sourceC1360) = raw20636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20636; decide +kernel
    rw [ha]
    exact (canonical20636 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1360 + difference 0 2) (sourceB1360 + difference 2 0) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1360 + difference 0 2) (sourceB1360 + difference 2 0) sourceC1360) = raw20450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20450; decide +kernel
    rw [ha]
    exact (canonical20450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1360 + difference 0 3) (sourceB1360 + difference 3 0) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1360 + difference 0 3) (sourceB1360 + difference 3 0) sourceC1360) = raw20451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20451; decide +kernel
    rw [ha]
    exact (canonical20451 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1360 + difference 0 4) (sourceB1360 + difference 4 0) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1360 + difference 0 4) (sourceB1360 + difference 4 0) sourceC1360) = raw20452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20452; decide +kernel
    rw [ha]
    exact (canonical20452 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1360 + difference 0 5) (sourceB1360 + difference 5 0) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1360 + difference 0 5) (sourceB1360 + difference 5 0) sourceC1360) = raw20453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20453; decide +kernel
    rw [ha]
    exact (canonical20453 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1360 + difference 1 0) (sourceB1360 + difference 0 1) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1471) := by
    have ha : (tripleCharges (sourceA1360 + difference 1 0) (sourceB1360 + difference 0 1) sourceC1360) = raw21550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21550; decide +kernel
    rw [ha]
    exact (canonical21550 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1360 + difference 1 2) (sourceB1360 + difference 2 1) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1361) := by
    have ha : (tripleCharges (sourceA1360 + difference 1 2) (sourceB1360 + difference 2 1) sourceC1360) = raw21551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21551; decide +kernel
    rw [ha]
    exact (canonical21551 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1360 + difference 1 3) (sourceB1360 + difference 3 1) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1361) := by
    have ha : (tripleCharges (sourceA1360 + difference 1 3) (sourceB1360 + difference 3 1) sourceC1360) = raw21552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21552; decide +kernel
    rw [ha]
    exact (canonical21552 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1360 + difference 1 4) (sourceB1360 + difference 4 1) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1373) := by
    have ha : (tripleCharges (sourceA1360 + difference 1 4) (sourceB1360 + difference 4 1) sourceC1360) = raw21553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21553; decide +kernel
    rw [ha]
    exact (canonical21553 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1360 + difference 1 5) (sourceB1360 + difference 5 1) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA1360 + difference 1 5) (sourceB1360 + difference 5 1) sourceC1360) = raw21347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21347; decide +kernel
    rw [ha]
    exact (canonical21347 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1360 + difference 2 0) (sourceB1360 + difference 0 2) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1478) := by
    have ha : (tripleCharges (sourceA1360 + difference 2 0) (sourceB1360 + difference 0 2) sourceC1360) = raw21554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21554; decide +kernel
    rw [ha]
    exact (canonical21554 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1360 + difference 2 1) (sourceB1360 + difference 1 2) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1360 + difference 2 1) (sourceB1360 + difference 1 2) sourceC1360) = raw20454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20454; decide +kernel
    rw [ha]
    exact (canonical20454 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1360 + difference 2 3) (sourceB1360 + difference 3 2) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1379) := by
    have ha : (tripleCharges (sourceA1360 + difference 2 3) (sourceB1360 + difference 3 2) sourceC1360) = raw21555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21555; decide +kernel
    rw [ha]
    exact (canonical21555 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1360 + difference 2 4) (sourceB1360 + difference 4 2) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1389) := by
    have ha : (tripleCharges (sourceA1360 + difference 2 4) (sourceB1360 + difference 4 2) sourceC1360) = raw21556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21556; decide +kernel
    rw [ha]
    exact (canonical21556 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1360 + difference 2 5) (sourceB1360 + difference 5 2) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1360 + difference 2 5) (sourceB1360 + difference 5 2) sourceC1360) = raw21352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21352; decide +kernel
    rw [ha]
    exact (canonical21352 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1360 + difference 3 0) (sourceB1360 + difference 0 3) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1478) := by
    have ha : (tripleCharges (sourceA1360 + difference 3 0) (sourceB1360 + difference 0 3) sourceC1360) = raw21557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21557; decide +kernel
    rw [ha]
    exact (canonical21557 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1360 + difference 3 1) (sourceB1360 + difference 1 3) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1360 + difference 3 1) (sourceB1360 + difference 1 3) sourceC1360) = raw20459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20459; decide +kernel
    rw [ha]
    exact (canonical20459 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1360 + difference 3 2) (sourceB1360 + difference 2 3) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1379) := by
    have ha : (tripleCharges (sourceA1360 + difference 3 2) (sourceB1360 + difference 2 3) sourceC1360) = raw21558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21558; decide +kernel
    rw [ha]
    exact (canonical21558 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1360 + difference 3 4) (sourceB1360 + difference 4 3) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1389) := by
    have ha : (tripleCharges (sourceA1360 + difference 3 4) (sourceB1360 + difference 4 3) sourceC1360) = raw21559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21559; decide +kernel
    rw [ha]
    exact (canonical21559 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1360 + difference 3 5) (sourceB1360 + difference 5 3) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1360 + difference 3 5) (sourceB1360 + difference 5 3) sourceC1360) = raw21357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21357; decide +kernel
    rw [ha]
    exact (canonical21357 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1360 + difference 4 0) (sourceB1360 + difference 0 4) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1484) := by
    have ha : (tripleCharges (sourceA1360 + difference 4 0) (sourceB1360 + difference 0 4) sourceC1360) = raw21364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21364; decide +kernel
    rw [ha]
    exact (canonical21364 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1360 + difference 4 1) (sourceB1360 + difference 1 4) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1450) := by
    have ha : (tripleCharges (sourceA1360 + difference 4 1) (sourceB1360 + difference 1 4) sourceC1360) = raw20464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20464; decide +kernel
    rw [ha]
    exact (canonical20464 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1360 + difference 4 2) (sourceB1360 + difference 2 4) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1397) := by
    have ha : (tripleCharges (sourceA1360 + difference 4 2) (sourceB1360 + difference 2 4) sourceC1360) = raw21365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21365; decide +kernel
    rw [ha]
    exact (canonical21365 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1360 + difference 4 3) (sourceB1360 + difference 3 4) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1397) := by
    have ha : (tripleCharges (sourceA1360 + difference 4 3) (sourceB1360 + difference 3 4) sourceC1360) = raw21366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21366; decide +kernel
    rw [ha]
    exact (canonical21366 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1360 + difference 4 5) (sourceB1360 + difference 5 4) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA1360 + difference 4 5) (sourceB1360 + difference 5 4) sourceC1360) = raw21560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21560; decide +kernel
    rw [ha]
    exact (canonical21560 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1360 + difference 5 0) (sourceB1360 + difference 0 5) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1485) := by
    have ha : (tripleCharges (sourceA1360 + difference 5 0) (sourceB1360 + difference 0 5) sourceC1360) = raw21561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21561; decide +kernel
    rw [ha]
    exact (canonical21561 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1360 + difference 5 1) (sourceB1360 + difference 1 5) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1452) := by
    have ha : (tripleCharges (sourceA1360 + difference 5 1) (sourceB1360 + difference 1 5) sourceC1360) = raw20469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20469; decide +kernel
    rw [ha]
    exact (canonical20469 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1360 + difference 5 2) (sourceB1360 + difference 2 5) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1399) := by
    have ha : (tripleCharges (sourceA1360 + difference 5 2) (sourceB1360 + difference 2 5) sourceC1360) = raw21562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21562; decide +kernel
    rw [ha]
    exact (canonical21562 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1360 + difference 5 3) (sourceB1360 + difference 3 5) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1399) := by
    have ha : (tripleCharges (sourceA1360 + difference 5 3) (sourceB1360 + difference 3 5) sourceC1360) = raw20980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20980; decide +kernel
    rw [ha]
    exact (canonical20980 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1360 + difference 5 4) (sourceB1360 + difference 4 5) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1417) := by
    have ha : (tripleCharges (sourceA1360 + difference 5 4) (sourceB1360 + difference 4 5) sourceC1360) = raw20624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20624; decide +kernel
    rw [ha]
    exact (canonical20624 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1360 sourceB1360 sourceC1360
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1360, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1361 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1361 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1361 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceForm1361 : Integer.Sparse Master := [(Sum.inr 1037, 1), (Sum.inr 2018, 2), (Sum.inr 2103, 1), (Sum.inr 2208, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

theorem sourceEq1361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1361 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 0) (sourceB1361 + difference 0 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 0) (sourceB1361 + difference 0 0) sourceC1361) = raw21563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw21563; decide +kernel
    rw [ha]
    exact (canonical21563 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 1) (sourceB1361 + difference 1 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2103) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 1) (sourceB1361 + difference 1 0) sourceC1361) = raw21564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw21564; decide +kernel
    rw [ha]
    exact (canonical21564 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 2) (sourceB1361 + difference 2 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 2) (sourceB1361 + difference 2 0) sourceC1361) = raw21565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw21565; decide +kernel
    rw [ha]
    exact (canonical21565 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 3) (sourceB1361 + difference 3 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 3) (sourceB1361 + difference 3 0) sourceC1361) = raw21566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw21566; decide +kernel
    rw [ha]
    exact (canonical21566 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 4) (sourceB1361 + difference 4 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 4) (sourceB1361 + difference 4 0) sourceC1361) = raw19875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw19875; decide +kernel
    rw [ha]
    exact (canonical19875 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 5) (sourceB1361 + difference 5 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 5) (sourceB1361 + difference 5 0) sourceC1361) = raw21567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw21567; decide +kernel
    rw [ha]
    exact (canonical21567 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1361 + sourceB1361) sourceC1361) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1361 + sourceB1361) sourceC1361) = raw19876 := by
      apply Matrix.ext; unfold doubleCharges sourceA1361 sourceB1361 sourceC1361 raw19876; decide +kernel
    rw [ha]
    exact (canonical19876 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1361 sourceB1361 sourceC1361
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1361, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1362 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1362 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1362 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceForm1362 : Integer.Sparse Master := [(Sum.inr 594, 1), (Sum.inr 916, 2), (Sum.inr 1007, 1), (Sum.inr 1037, 1), (Sum.inr 1074, 1), (Sum.inr 4081, -1)]

theorem sourceEq1362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1362 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 0) (sourceB1362 + difference 0 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 594) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 0) (sourceB1362 + difference 0 1) sourceC1362) = raw21568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw21568; decide +kernel
    rw [ha]
    exact (canonical21568 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 1) (sourceB1362 + difference 1 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 1) (sourceB1362 + difference 1 1) sourceC1362) = raw21563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw21563; decide +kernel
    rw [ha]
    exact (canonical21563 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 2) (sourceB1362 + difference 2 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 916) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 2) (sourceB1362 + difference 2 1) sourceC1362) = raw21569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw21569; decide +kernel
    rw [ha]
    exact (canonical21569 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 3) (sourceB1362 + difference 3 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 916) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 3) (sourceB1362 + difference 3 1) sourceC1362) = raw21570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw21570; decide +kernel
    rw [ha]
    exact (canonical21570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 4) (sourceB1362 + difference 4 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1007) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 4) (sourceB1362 + difference 4 1) sourceC1362) = raw19881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw19881; decide +kernel
    rw [ha]
    exact (canonical19881 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 5) (sourceB1362 + difference 5 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 5) (sourceB1362 + difference 5 1) sourceC1362) = raw21571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw21571; decide +kernel
    rw [ha]
    exact (canonical21571 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1362 + sourceB1362) sourceC1362) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1362 + sourceB1362) sourceC1362) = raw19876 := by
      apply Matrix.ext; unfold doubleCharges sourceA1362 sourceB1362 sourceC1362 raw19876; decide +kernel
    rw [ha]
    exact (canonical19876 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1362 sourceB1362 sourceC1362
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1362, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1363 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1363 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1363 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceForm1363 : Integer.Sparse Master := [(Sum.inr 1033, 2), (Sum.inr 1037, 1), (Sum.inr 1048, 1), (Sum.inr 1074, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

theorem sourceEq1363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1363 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1363 + difference 0 5) (sourceB1363 + difference 5 0) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1363 + difference 0 5) (sourceB1363 + difference 5 0) sourceC1363) = raw21567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21567; decide +kernel
    rw [ha]
    exact (canonical21567 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1363 + difference 1 5) (sourceB1363 + difference 5 1) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1363 + difference 1 5) (sourceB1363 + difference 5 1) sourceC1363) = raw21571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21571; decide +kernel
    rw [ha]
    exact (canonical21571 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1363 + difference 2 5) (sourceB1363 + difference 5 2) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1033) := by
    have ha : (tripleCharges (sourceA1363 + difference 2 5) (sourceB1363 + difference 5 2) sourceC1363) = raw21572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21572; decide +kernel
    rw [ha]
    exact (canonical21572 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1363 + difference 3 5) (sourceB1363 + difference 5 3) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1033) := by
    have ha : (tripleCharges (sourceA1363 + difference 3 5) (sourceB1363 + difference 5 3) sourceC1363) = raw21573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21573; decide +kernel
    rw [ha]
    exact (canonical21573 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1363 + difference 4 5) (sourceB1363 + difference 5 4) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1048) := by
    have ha : (tripleCharges (sourceA1363 + difference 4 5) (sourceB1363 + difference 5 4) sourceC1363) = raw21574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21574; decide +kernel
    rw [ha]
    exact (canonical21574 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1363 + difference 5 5) (sourceB1363 + difference 5 5) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1363 + difference 5 5) (sourceB1363 + difference 5 5) sourceC1363) = raw21563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21563; decide +kernel
    rw [ha]
    exact (canonical21563 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1363 + sourceB1363) sourceC1363) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1363 + sourceB1363) sourceC1363) = raw19876 := by
      apply Matrix.ext; unfold doubleCharges sourceA1363 sourceB1363 sourceC1363 raw19876; decide +kernel
    rw [ha]
    exact (canonical19876 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1363 sourceB1363 sourceC1363
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1363, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1364 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB1364 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceC1364 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1364 : Integer.Sparse Master := [(Sum.inr 731, 2), (Sum.inr 735, 1), (Sum.inr 741, 1), (Sum.inr 809, 1), (Sum.inr 1647, 1), (Sum.inr 4070, -1)]

theorem sourceEq1364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1364 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1364 + difference 0 0) (sourceB1364 + difference 0 0) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1364 + difference 0 0) (sourceB1364 + difference 0 0) sourceC1364) = raw20643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw20643; decide +kernel
    rw [ha]
    exact (canonical20643 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1364 + difference 1 0) (sourceB1364 + difference 0 1) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 741) := by
    have ha : (tripleCharges (sourceA1364 + difference 1 0) (sourceB1364 + difference 0 1) sourceC1364) = raw21575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw21575; decide +kernel
    rw [ha]
    exact (canonical21575 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1364 + difference 2 0) (sourceB1364 + difference 0 2) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 731) := by
    have ha : (tripleCharges (sourceA1364 + difference 2 0) (sourceB1364 + difference 0 2) sourceC1364) = raw21576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw21576; decide +kernel
    rw [ha]
    exact (canonical21576 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1364 + difference 3 0) (sourceB1364 + difference 0 3) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 731) := by
    have ha : (tripleCharges (sourceA1364 + difference 3 0) (sourceB1364 + difference 0 3) sourceC1364) = raw21577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw21577; decide +kernel
    rw [ha]
    exact (canonical21577 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1364 + difference 4 0) (sourceB1364 + difference 0 4) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1364 + difference 4 0) (sourceB1364 + difference 0 4) sourceC1364) = raw21578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw21578; decide +kernel
    rw [ha]
    exact (canonical21578 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1364 + difference 5 0) (sourceB1364 + difference 0 5) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 735) := by
    have ha : (tripleCharges (sourceA1364 + difference 5 0) (sourceB1364 + difference 0 5) sourceC1364) = raw21579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw21579; decide +kernel
    rw [ha]
    exact (canonical21579 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1364 + sourceB1364) sourceC1364) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1364 + sourceB1364) sourceC1364) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1364 sourceB1364 sourceC1364 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1364 sourceB1364 sourceC1364
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1364, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1365 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1365 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceC1365 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceForm1365 : Integer.Sparse Master := [(Sum.inr 983, 1), (Sum.inr 1915, 1), (Sum.inr 1988, 1), (Sum.inr 2080, 1), (Sum.inr 2197, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

theorem sourceEq1365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1365 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1365 + difference 0 0) (sourceB1365 + difference 0 0) sourceC1365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA1365 + difference 0 0) (sourceB1365 + difference 0 0) sourceC1365) = raw21580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1365 sourceB1365 sourceC1365 difference raw21580; decide +kernel
    rw [ha]
    exact (canonical21580 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1365 + difference 0 1) (sourceB1365 + difference 1 0) sourceC1365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2080) := by
    have ha : (tripleCharges (sourceA1365 + difference 0 1) (sourceB1365 + difference 1 0) sourceC1365) = raw21581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1365 sourceB1365 sourceC1365 difference raw21581; decide +kernel
    rw [ha]
    exact (canonical21581 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1365 + difference 0 2) (sourceB1365 + difference 2 0) sourceC1365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1988) := by
    have ha : (tripleCharges (sourceA1365 + difference 0 2) (sourceB1365 + difference 2 0) sourceC1365) = raw21582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1365 sourceB1365 sourceC1365 difference raw21582; decide +kernel
    rw [ha]
    exact (canonical21582 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1365 + difference 0 3) (sourceB1365 + difference 3 0) sourceC1365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA1365 + difference 0 3) (sourceB1365 + difference 3 0) sourceC1365) = raw21583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1365 sourceB1365 sourceC1365 difference raw21583; decide +kernel
    rw [ha]
    exact (canonical21583 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1365 + difference 0 4) (sourceB1365 + difference 4 0) sourceC1365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA1365 + difference 0 4) (sourceB1365 + difference 4 0) sourceC1365) = raw21584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1365 sourceB1365 sourceC1365 difference raw21584; decide +kernel
    rw [ha]
    exact (canonical21584 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1365 + difference 0 5) (sourceB1365 + difference 5 0) sourceC1365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1365 + difference 0 5) (sourceB1365 + difference 5 0) sourceC1365) = raw21585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1365 sourceB1365 sourceC1365 difference raw21585; decide +kernel
    rw [ha]
    exact (canonical21585 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1365 + sourceB1365) sourceC1365) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1365 + sourceB1365) sourceC1365) = raw21586 := by
      apply Matrix.ext; unfold doubleCharges sourceA1365 sourceB1365 sourceC1365 raw21586; decide +kernel
    rw [ha]
    exact (canonical21586 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1365 sourceB1365 sourceC1365
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1365, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1366 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1366 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceC1366 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceForm1366 : Integer.Sparse Master := [(Sum.inr 978, 1), (Sum.inr 983, 1), (Sum.inr 985, 1), (Sum.inr 1005, 1), (Sum.inr 1036, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

theorem sourceEq1366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1366 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1366 + difference 0 5) (sourceB1366 + difference 5 0) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1366 + difference 0 5) (sourceB1366 + difference 5 0) sourceC1366) = raw21585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21585; decide +kernel
    rw [ha]
    exact (canonical21585 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1366 + difference 1 5) (sourceB1366 + difference 5 1) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1366 + difference 1 5) (sourceB1366 + difference 5 1) sourceC1366) = raw21587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21587; decide +kernel
    rw [ha]
    exact (canonical21587 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1366 + difference 2 5) (sourceB1366 + difference 5 2) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 978) := by
    have ha : (tripleCharges (sourceA1366 + difference 2 5) (sourceB1366 + difference 5 2) sourceC1366) = raw21588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21588; decide +kernel
    rw [ha]
    exact (canonical21588 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1366 + difference 3 5) (sourceB1366 + difference 5 3) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1036) := by
    have ha : (tripleCharges (sourceA1366 + difference 3 5) (sourceB1366 + difference 5 3) sourceC1366) = raw21589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21589; decide +kernel
    rw [ha]
    exact (canonical21589 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1366 + difference 4 5) (sourceB1366 + difference 5 4) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1366 + difference 4 5) (sourceB1366 + difference 5 4) sourceC1366) = raw21590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21590; decide +kernel
    rw [ha]
    exact (canonical21590 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1366 + difference 5 5) (sourceB1366 + difference 5 5) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA1366 + difference 5 5) (sourceB1366 + difference 5 5) sourceC1366) = raw21580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21580; decide +kernel
    rw [ha]
    exact (canonical21580 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1366 + sourceB1366) sourceC1366) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1366 + sourceB1366) sourceC1366) = raw21586 := by
      apply Matrix.ext; unfold doubleCharges sourceA1366 sourceB1366 sourceC1366 raw21586; decide +kernel
    rw [ha]
    exact (canonical21586 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1366 sourceB1366 sourceC1366
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1366, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1367 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1367 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1367 : Charge := ![3, -1, 0, 1, -1, -2]
def sourceForm1367 : Integer.Sparse Master := [(Sum.inr 982, 1), (Sum.inr 1914, 1), (Sum.inr 1987, 1), (Sum.inr 2079, 1), (Sum.inr 2193, 1), (Sum.inr 2205, 1), (Sum.inr 4080, -1)]

theorem sourceEq1367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1367 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 0) (sourceB1367 + difference 0 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 0) (sourceB1367 + difference 0 0) sourceC1367) = raw21591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21591; decide +kernel
    rw [ha]
    exact (canonical21591 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 1) (sourceB1367 + difference 1 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 1) (sourceB1367 + difference 1 0) sourceC1367) = raw21592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21592; decide +kernel
    rw [ha]
    exact (canonical21592 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 2) (sourceB1367 + difference 2 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 2) (sourceB1367 + difference 2 0) sourceC1367) = raw21593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21593; decide +kernel
    rw [ha]
    exact (canonical21593 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 3) (sourceB1367 + difference 3 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 3) (sourceB1367 + difference 3 0) sourceC1367) = raw21594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21594; decide +kernel
    rw [ha]
    exact (canonical21594 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 4) (sourceB1367 + difference 4 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 4) (sourceB1367 + difference 4 0) sourceC1367) = raw21595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21595; decide +kernel
    rw [ha]
    exact (canonical21595 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 5) (sourceB1367 + difference 5 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 5) (sourceB1367 + difference 5 0) sourceC1367) = raw21596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21596; decide +kernel
    rw [ha]
    exact (canonical21596 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1367 + sourceB1367) sourceC1367) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1367 + sourceB1367) sourceC1367) = raw21597 := by
      apply Matrix.ext; unfold doubleCharges sourceA1367 sourceB1367 sourceC1367 raw21597; decide +kernel
    rw [ha]
    exact (canonical21597 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1367 sourceB1367 sourceC1367
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1367, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1368 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1368 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1368 : Charge := ![3, -1, 0, 1, -1, -2]
def sourceForm1368 : Integer.Sparse Master := [(Sum.inr 572, 1), (Sum.inr 886, 1), (Sum.inr 900, 1), (Sum.inr 982, 2), (Sum.inr 1004, 1), (Sum.inr 4080, -1)]

theorem sourceEq1368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1368 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1368 + difference 1 0) (sourceB1368 + difference 0 1) sourceC1368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 572) := by
    have ha : (tripleCharges (sourceA1368 + difference 1 0) (sourceB1368 + difference 0 1) sourceC1368) = raw21598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1368 sourceB1368 sourceC1368 difference raw21598; decide +kernel
    rw [ha]
    exact (canonical21598 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1368 + difference 1 1) (sourceB1368 + difference 1 1) sourceC1368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1368 + difference 1 1) (sourceB1368 + difference 1 1) sourceC1368) = raw21591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1368 sourceB1368 sourceC1368 difference raw21591; decide +kernel
    rw [ha]
    exact (canonical21591 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1368 + difference 1 2) (sourceB1368 + difference 2 1) sourceC1368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 900) := by
    have ha : (tripleCharges (sourceA1368 + difference 1 2) (sourceB1368 + difference 2 1) sourceC1368) = raw21599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1368 sourceB1368 sourceC1368 difference raw21599; decide +kernel
    rw [ha]
    exact (canonical21599 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1368 + difference 1 3) (sourceB1368 + difference 3 1) sourceC1368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 886) := by
    have ha : (tripleCharges (sourceA1368 + difference 1 3) (sourceB1368 + difference 3 1) sourceC1368) = raw21600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1368 sourceB1368 sourceC1368 difference raw21600; decide +kernel
    rw [ha]
    exact (canonical21600 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1368 + difference 1 4) (sourceB1368 + difference 4 1) sourceC1368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1368 + difference 1 4) (sourceB1368 + difference 4 1) sourceC1368) = raw21601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1368 sourceB1368 sourceC1368 difference raw21601; decide +kernel
    rw [ha]
    exact (canonical21601 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1368 + difference 1 5) (sourceB1368 + difference 5 1) sourceC1368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1004) := by
    have ha : (tripleCharges (sourceA1368 + difference 1 5) (sourceB1368 + difference 5 1) sourceC1368) = raw21602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1368 sourceB1368 sourceC1368 difference raw21602; decide +kernel
    rw [ha]
    exact (canonical21602 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1368 + sourceB1368) sourceC1368) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1368 + sourceB1368) sourceC1368) = raw21597 := by
      apply Matrix.ext; unfold doubleCharges sourceA1368 sourceB1368 sourceC1368 raw21597; decide +kernel
    rw [ha]
    exact (canonical21597 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1368 sourceB1368 sourceC1368
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1368, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1369 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1369 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1369 : Charge := ![3, -1, 0, 1, -1, -2]
def sourceForm1369 : Integer.Sparse Master := [(Sum.inr 865, 1), (Sum.inr 871, 1), (Sum.inr 873, 1), (Sum.inr 886, 1), (Sum.inr 982, 1), (Sum.inr 1914, 1), (Sum.inr 4080, -1)]

theorem sourceEq1369 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1369 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1369 + difference 0 3) (sourceB1369 + difference 3 0) sourceC1369) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA1369 + difference 0 3) (sourceB1369 + difference 3 0) sourceC1369) = raw21594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1369 sourceB1369 sourceC1369 difference raw21594; decide +kernel
    rw [ha]
    exact (canonical21594 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1369 + difference 1 3) (sourceB1369 + difference 3 1) sourceC1369) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 886) := by
    have ha : (tripleCharges (sourceA1369 + difference 1 3) (sourceB1369 + difference 3 1) sourceC1369) = raw21600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1369 sourceB1369 sourceC1369 difference raw21600; decide +kernel
    rw [ha]
    exact (canonical21600 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1369 + difference 2 3) (sourceB1369 + difference 3 2) sourceC1369) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 865) := by
    have ha : (tripleCharges (sourceA1369 + difference 2 3) (sourceB1369 + difference 3 2) sourceC1369) = raw21603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1369 sourceB1369 sourceC1369 difference raw21603; decide +kernel
    rw [ha]
    exact (canonical21603 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1369 + difference 3 3) (sourceB1369 + difference 3 3) sourceC1369) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1369 + difference 3 3) (sourceB1369 + difference 3 3) sourceC1369) = raw21591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1369 sourceB1369 sourceC1369 difference raw21591; decide +kernel
    rw [ha]
    exact (canonical21591 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1369 + difference 4 3) (sourceB1369 + difference 3 4) sourceC1369) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA1369 + difference 4 3) (sourceB1369 + difference 3 4) sourceC1369) = raw21604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1369 sourceB1369 sourceC1369 difference raw21604; decide +kernel
    rw [ha]
    exact (canonical21604 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1369 + difference 5 3) (sourceB1369 + difference 3 5) sourceC1369) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1369 + difference 5 3) (sourceB1369 + difference 3 5) sourceC1369) = raw21605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1369 sourceB1369 sourceC1369 difference raw21605; decide +kernel
    rw [ha]
    exact (canonical21605 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1369 + sourceB1369) sourceC1369) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1369 + sourceB1369) sourceC1369) = raw21597 := by
      apply Matrix.ext; unfold doubleCharges sourceA1369 sourceB1369 sourceC1369 raw21597; decide +kernel
    rw [ha]
    exact (canonical21597 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1369 sourceB1369 sourceC1369
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1369, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1370 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1370 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1370 : Charge := ![3, -1, 0, 1, -1, -2]
def sourceForm1370 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 982, 1), (Sum.inr 985, 1), (Sum.inr 1004, 1), (Sum.inr 1035, 1), (Sum.inr 2205, 1), (Sum.inr 4080, -1)]

theorem sourceEq1370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1370 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1370 + difference 0 5) (sourceB1370 + difference 5 0) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA1370 + difference 0 5) (sourceB1370 + difference 5 0) sourceC1370) = raw21596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21596; decide +kernel
    rw [ha]
    exact (canonical21596 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1370 + difference 1 5) (sourceB1370 + difference 5 1) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1004) := by
    have ha : (tripleCharges (sourceA1370 + difference 1 5) (sourceB1370 + difference 5 1) sourceC1370) = raw21602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21602; decide +kernel
    rw [ha]
    exact (canonical21602 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1370 + difference 2 5) (sourceB1370 + difference 5 2) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1370 + difference 2 5) (sourceB1370 + difference 5 2) sourceC1370) = raw21606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21606; decide +kernel
    rw [ha]
    exact (canonical21606 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1370 + difference 3 5) (sourceB1370 + difference 5 3) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1370 + difference 3 5) (sourceB1370 + difference 5 3) sourceC1370) = raw21607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21607; decide +kernel
    rw [ha]
    exact (canonical21607 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1370 + difference 4 5) (sourceB1370 + difference 5 4) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1370 + difference 4 5) (sourceB1370 + difference 5 4) sourceC1370) = raw21608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21608; decide +kernel
    rw [ha]
    exact (canonical21608 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1370 + difference 5 5) (sourceB1370 + difference 5 5) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1370 + difference 5 5) (sourceB1370 + difference 5 5) sourceC1370) = raw21591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21591; decide +kernel
    rw [ha]
    exact (canonical21591 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1370 + sourceB1370) sourceC1370) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1370 + sourceB1370) sourceC1370) = raw21597 := by
      apply Matrix.ext; unfold doubleCharges sourceA1370 sourceB1370 sourceC1370 raw21597; decide +kernel
    rw [ha]
    exact (canonical21597 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1370 sourceB1370 sourceC1370
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1370, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1371 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB1371 : Charge := ![3, -1, 0, 1, -1, -2]
def sourceC1371 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1371 : Integer.Sparse Master := [(Sum.inr 709, 1), (Sum.inr 714, 1), (Sum.inr 716, 1), (Sum.inr 721, 1), (Sum.inr 851, 1), (Sum.inr 1617, 1), (Sum.inr 4070, -1)]

theorem sourceEq1371 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1371 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1371 + difference 0 0) (sourceB1371 + difference 0 0) sourceC1371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1371 + difference 0 0) (sourceB1371 + difference 0 0) sourceC1371) = raw20840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1371 sourceB1371 sourceC1371 difference raw20840; decide +kernel
    rw [ha]
    exact (canonical20840 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1371 + difference 1 0) (sourceB1371 + difference 0 1) sourceC1371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 721) := by
    have ha : (tripleCharges (sourceA1371 + difference 1 0) (sourceB1371 + difference 0 1) sourceC1371) = raw21609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1371 sourceB1371 sourceC1371 difference raw21609; decide +kernel
    rw [ha]
    exact (canonical21609 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1371 + difference 2 0) (sourceB1371 + difference 0 2) sourceC1371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 709) := by
    have ha : (tripleCharges (sourceA1371 + difference 2 0) (sourceB1371 + difference 0 2) sourceC1371) = raw21610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1371 sourceB1371 sourceC1371 difference raw21610; decide +kernel
    rw [ha]
    exact (canonical21610 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1371 + difference 3 0) (sourceB1371 + difference 0 3) sourceC1371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 851) := by
    have ha : (tripleCharges (sourceA1371 + difference 3 0) (sourceB1371 + difference 0 3) sourceC1371) = raw21372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1371 sourceB1371 sourceC1371 difference raw21372; decide +kernel
    rw [ha]
    exact (canonical21372 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1371 + difference 4 0) (sourceB1371 + difference 0 4) sourceC1371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 716) := by
    have ha : (tripleCharges (sourceA1371 + difference 4 0) (sourceB1371 + difference 0 4) sourceC1371) = raw21611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1371 sourceB1371 sourceC1371 difference raw21611; decide +kernel
    rw [ha]
    exact (canonical21611 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1371 + difference 5 0) (sourceB1371 + difference 0 5) sourceC1371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 714) := by
    have ha : (tripleCharges (sourceA1371 + difference 5 0) (sourceB1371 + difference 0 5) sourceC1371) = raw21612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1371 sourceB1371 sourceC1371 difference raw21612; decide +kernel
    rw [ha]
    exact (canonical21612 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1371 + sourceB1371) sourceC1371) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1371 + sourceB1371) sourceC1371) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1371 sourceB1371 sourceC1371 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1371 sourceB1371 sourceC1371
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1371, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1372 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB1372 : Charge := ![3, -1, 0, 1, -1, -2]
def sourceC1372 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1372 : Integer.Sparse Master := [(Sum.inr 714, 1), (Sum.inr 1543, 1), (Sum.inr 1580, 1), (Sum.inr 1599, 1), (Sum.inr 1617, 1), (Sum.inr 1625, 1), (Sum.inr 4070, -1)]

theorem sourceEq1372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1372 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1372 + difference 5 0) (sourceB1372 + difference 0 5) sourceC1372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 714) := by
    have ha : (tripleCharges (sourceA1372 + difference 5 0) (sourceB1372 + difference 0 5) sourceC1372) = raw21612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1372 sourceB1372 sourceC1372 difference raw21612; decide +kernel
    rw [ha]
    exact (canonical21612 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1372 + difference 5 1) (sourceB1372 + difference 1 5) sourceC1372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1625) := by
    have ha : (tripleCharges (sourceA1372 + difference 5 1) (sourceB1372 + difference 1 5) sourceC1372) = raw20843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1372 sourceB1372 sourceC1372 difference raw20843; decide +kernel
    rw [ha]
    exact (canonical20843 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1372 + difference 5 2) (sourceB1372 + difference 2 5) sourceC1372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1580) := by
    have ha : (tripleCharges (sourceA1372 + difference 5 2) (sourceB1372 + difference 2 5) sourceC1372) = raw21067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1372 sourceB1372 sourceC1372 difference raw21067; decide +kernel
    rw [ha]
    exact (canonical21067 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1372 + difference 5 3) (sourceB1372 + difference 3 5) sourceC1372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1543) := by
    have ha : (tripleCharges (sourceA1372 + difference 5 3) (sourceB1372 + difference 3 5) sourceC1372) = raw21029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1372 sourceB1372 sourceC1372 difference raw21029; decide +kernel
    rw [ha]
    exact (canonical21029 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1372 + difference 5 4) (sourceB1372 + difference 4 5) sourceC1372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1372 + difference 5 4) (sourceB1372 + difference 4 5) sourceC1372) = raw20995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1372 sourceB1372 sourceC1372 difference raw20995; decide +kernel
    rw [ha]
    exact (canonical20995 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1372 + difference 5 5) (sourceB1372 + difference 5 5) sourceC1372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1372 + difference 5 5) (sourceB1372 + difference 5 5) sourceC1372) = raw20840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1372 sourceB1372 sourceC1372 difference raw20840; decide +kernel
    rw [ha]
    exact (canonical20840 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1372 + sourceB1372) sourceC1372) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1372 + sourceB1372) sourceC1372) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1372 sourceB1372 sourceC1372 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1372 sourceB1372 sourceC1372
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1372, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1373 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1373 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1373 : Charge := ![3, -1, 0, 1, 0, -3]
def sourceForm1373 : Integer.Sparse Master := [(Sum.inr 979, 1), (Sum.inr 1911, 1), (Sum.inr 1986, 1), (Sum.inr 2018, 1), (Sum.inr 2203, 1), (Sum.inr 2208, 1), (Sum.inr 4081, -1)]

theorem sourceEq1373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1373 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 0) (sourceB1373 + difference 0 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 0) (sourceB1373 + difference 0 0) sourceC1373) = raw21613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21613; decide +kernel
    rw [ha]
    exact (canonical21613 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 1) (sourceB1373 + difference 1 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 1) (sourceB1373 + difference 1 0) sourceC1373) = raw21614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21614; decide +kernel
    rw [ha]
    exact (canonical21614 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 2) (sourceB1373 + difference 2 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1986) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 2) (sourceB1373 + difference 2 0) sourceC1373) = raw21615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21615; decide +kernel
    rw [ha]
    exact (canonical21615 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 3) (sourceB1373 + difference 3 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 3) (sourceB1373 + difference 3 0) sourceC1373) = raw21616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21616; decide +kernel
    rw [ha]
    exact (canonical21616 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 4) (sourceB1373 + difference 4 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 4) (sourceB1373 + difference 4 0) sourceC1373) = raw21617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21617; decide +kernel
    rw [ha]
    exact (canonical21617 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 5) (sourceB1373 + difference 5 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 5) (sourceB1373 + difference 5 0) sourceC1373) = raw21618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21618; decide +kernel
    rw [ha]
    exact (canonical21618 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1373 + sourceB1373) sourceC1373) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1373 + sourceB1373) sourceC1373) = raw21619 := by
      apply Matrix.ext; unfold doubleCharges sourceA1373 sourceB1373 sourceC1373 raw21619; decide +kernel
    rw [ha]
    exact (canonical21619 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1373 sourceB1373 sourceC1373
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1373, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1374 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1374 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1374 : Charge := ![3, -1, 0, 1, 0, -3]
def sourceForm1374 : Integer.Sparse Master := [(Sum.inr 568, 1), (Sum.inr 880, 1), (Sum.inr 898, 1), (Sum.inr 979, 1), (Sum.inr 999, 1), (Sum.inr 1007, 1), (Sum.inr 4081, -1)]

theorem sourceEq1374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1374 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1374 + difference 1 0) (sourceB1374 + difference 0 1) sourceC1374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 568) := by
    have ha : (tripleCharges (sourceA1374 + difference 1 0) (sourceB1374 + difference 0 1) sourceC1374) = raw21620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1374 sourceB1374 sourceC1374 difference raw21620; decide +kernel
    rw [ha]
    exact (canonical21620 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1374 + difference 1 1) (sourceB1374 + difference 1 1) sourceC1374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1374 + difference 1 1) (sourceB1374 + difference 1 1) sourceC1374) = raw21613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1374 sourceB1374 sourceC1374 difference raw21613; decide +kernel
    rw [ha]
    exact (canonical21613 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1374 + difference 1 2) (sourceB1374 + difference 2 1) sourceC1374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 898) := by
    have ha : (tripleCharges (sourceA1374 + difference 1 2) (sourceB1374 + difference 2 1) sourceC1374) = raw21621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1374 sourceB1374 sourceC1374 difference raw21621; decide +kernel
    rw [ha]
    exact (canonical21621 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1374 + difference 1 3) (sourceB1374 + difference 3 1) sourceC1374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 880) := by
    have ha : (tripleCharges (sourceA1374 + difference 1 3) (sourceB1374 + difference 3 1) sourceC1374) = raw21622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1374 sourceB1374 sourceC1374 difference raw21622; decide +kernel
    rw [ha]
    exact (canonical21622 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1374 + difference 1 4) (sourceB1374 + difference 4 1) sourceC1374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1007) := by
    have ha : (tripleCharges (sourceA1374 + difference 1 4) (sourceB1374 + difference 4 1) sourceC1374) = raw21623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1374 sourceB1374 sourceC1374 difference raw21623; decide +kernel
    rw [ha]
    exact (canonical21623 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1374 + difference 1 5) (sourceB1374 + difference 5 1) sourceC1374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1374 + difference 1 5) (sourceB1374 + difference 5 1) sourceC1374) = raw21624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1374 sourceB1374 sourceC1374 difference raw21624; decide +kernel
    rw [ha]
    exact (canonical21624 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1374 + sourceB1374) sourceC1374) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1374 + sourceB1374) sourceC1374) = raw21619 := by
      apply Matrix.ext; unfold doubleCharges sourceA1374 sourceB1374 sourceC1374 raw21619; decide +kernel
    rw [ha]
    exact (canonical21619 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1374 sourceB1374 sourceC1374
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1374, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1375 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1375 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1375 : Charge := ![3, -1, 0, 1, 0, -3]
def sourceForm1375 : Integer.Sparse Master := [(Sum.inr 864, 1), (Sum.inr 867, 1), (Sum.inr 872, 1), (Sum.inr 880, 1), (Sum.inr 979, 1), (Sum.inr 1911, 1), (Sum.inr 4081, -1)]

theorem sourceEq1375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1375 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1375 + difference 0 3) (sourceB1375 + difference 3 0) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA1375 + difference 0 3) (sourceB1375 + difference 3 0) sourceC1375) = raw21616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21616; decide +kernel
    rw [ha]
    exact (canonical21616 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1375 + difference 1 3) (sourceB1375 + difference 3 1) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 880) := by
    have ha : (tripleCharges (sourceA1375 + difference 1 3) (sourceB1375 + difference 3 1) sourceC1375) = raw21622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21622; decide +kernel
    rw [ha]
    exact (canonical21622 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1375 + difference 2 3) (sourceB1375 + difference 3 2) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 864) := by
    have ha : (tripleCharges (sourceA1375 + difference 2 3) (sourceB1375 + difference 3 2) sourceC1375) = raw21625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21625; decide +kernel
    rw [ha]
    exact (canonical21625 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1375 + difference 3 3) (sourceB1375 + difference 3 3) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1375 + difference 3 3) (sourceB1375 + difference 3 3) sourceC1375) = raw21613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21613; decide +kernel
    rw [ha]
    exact (canonical21613 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1375 + difference 4 3) (sourceB1375 + difference 3 4) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 872) := by
    have ha : (tripleCharges (sourceA1375 + difference 4 3) (sourceB1375 + difference 3 4) sourceC1375) = raw21626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21626; decide +kernel
    rw [ha]
    exact (canonical21626 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1375 + difference 5 3) (sourceB1375 + difference 3 5) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 867) := by
    have ha : (tripleCharges (sourceA1375 + difference 5 3) (sourceB1375 + difference 3 5) sourceC1375) = raw21627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21627; decide +kernel
    rw [ha]
    exact (canonical21627 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1375 + sourceB1375) sourceC1375) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1375 + sourceB1375) sourceC1375) = raw21619 := by
      apply Matrix.ext; unfold doubleCharges sourceA1375 sourceB1375 sourceC1375 raw21619; decide +kernel
    rw [ha]
    exact (canonical21619 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1375 sourceB1375 sourceC1375
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1375, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
