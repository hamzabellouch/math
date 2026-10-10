import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical95
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical96
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical97
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical101
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical104
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical107
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical136
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical137
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical141
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical142
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical144
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical145
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical146
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical147

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1088 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1088 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC1088 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceForm1088 : Integer.Sparse Master := [(Sum.inr 5144, 1), (Sum.inr 5147, 1), (Sum.inr 5151, 1), (Sum.inr 5163, 1), (Sum.inr 5184, 1), (Sum.inr 5188, 1), (Sum.inr 5198, 1), (Sum.inr 5231, 1), (Sum.inr 5232, 1), (Sum.inr 5233, 1), (Sum.inr 5258, 1), (Sum.inr 5291, 1), (Sum.inr 5299, 1), (Sum.inr 5381, 1), (Sum.inr 5384, 1), (Sum.inr 5400, 1), (Sum.inr 5409, 1), (Sum.inr 5420, 1), (Sum.inr 5423, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5441, 1), (Sum.inr 5446, 1), (Sum.inr 5449, 1), (Sum.inr 5451, 1), (Sum.inr 5473, 1)]

theorem sourceEq1088 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1088 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1088 + difference 0 1) (sourceB1088 + difference 1 0) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA1088 + difference 0 1) (sourceB1088 + difference 1 0) sourceC1088) = raw18138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18138; decide +kernel
    rw [ha]
    exact (canonical18138 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1088 + difference 0 2) (sourceB1088 + difference 2 0) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1088 + difference 0 2) (sourceB1088 + difference 2 0) sourceC1088) = raw18139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18139; decide +kernel
    rw [ha]
    exact (canonical18139 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1088 + difference 0 3) (sourceB1088 + difference 3 0) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1088 + difference 0 3) (sourceB1088 + difference 3 0) sourceC1088) = raw18140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18140; decide +kernel
    rw [ha]
    exact (canonical18140 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1088 + difference 0 4) (sourceB1088 + difference 4 0) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1088 + difference 0 4) (sourceB1088 + difference 4 0) sourceC1088) = raw18141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18141; decide +kernel
    rw [ha]
    exact (canonical18141 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1088 + difference 0 5) (sourceB1088 + difference 5 0) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1088 + difference 0 5) (sourceB1088 + difference 5 0) sourceC1088) = raw18142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18142; decide +kernel
    rw [ha]
    exact (canonical18142 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1088 + difference 1 0) (sourceB1088 + difference 0 1) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1088 + difference 1 0) (sourceB1088 + difference 0 1) sourceC1088) = raw18143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18143; decide +kernel
    rw [ha]
    exact (canonical18143 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1088 + difference 1 2) (sourceB1088 + difference 2 1) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1088 + difference 1 2) (sourceB1088 + difference 2 1) sourceC1088) = raw9970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw9970; decide +kernel
    rw [ha]
    exact (canonical9970 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1088 + difference 1 3) (sourceB1088 + difference 3 1) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1088 + difference 1 3) (sourceB1088 + difference 3 1) sourceC1088) = raw9971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw9971; decide +kernel
    rw [ha]
    exact (canonical9971 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1088 + difference 1 4) (sourceB1088 + difference 4 1) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1088 + difference 1 4) (sourceB1088 + difference 4 1) sourceC1088) = raw9972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw9972; decide +kernel
    rw [ha]
    exact (canonical9972 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1088 + difference 1 5) (sourceB1088 + difference 5 1) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1088 + difference 1 5) (sourceB1088 + difference 5 1) sourceC1088) = raw9973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw9973; decide +kernel
    rw [ha]
    exact (canonical9973 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1088 + difference 2 0) (sourceB1088 + difference 0 2) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA1088 + difference 2 0) (sourceB1088 + difference 0 2) sourceC1088) = raw9980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw9980; decide +kernel
    rw [ha]
    exact (canonical9980 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1088 + difference 2 1) (sourceB1088 + difference 1 2) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA1088 + difference 2 1) (sourceB1088 + difference 1 2) sourceC1088) = raw18144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18144; decide +kernel
    rw [ha]
    exact (canonical18144 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1088 + difference 2 3) (sourceB1088 + difference 3 2) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1088 + difference 2 3) (sourceB1088 + difference 3 2) sourceC1088) = raw18145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18145; decide +kernel
    rw [ha]
    exact (canonical18145 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1088 + difference 2 4) (sourceB1088 + difference 4 2) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1088 + difference 2 4) (sourceB1088 + difference 4 2) sourceC1088) = raw18146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18146; decide +kernel
    rw [ha]
    exact (canonical18146 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1088 + difference 2 5) (sourceB1088 + difference 5 2) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1088 + difference 2 5) (sourceB1088 + difference 5 2) sourceC1088) = raw18147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18147; decide +kernel
    rw [ha]
    exact (canonical18147 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1088 + difference 3 0) (sourceB1088 + difference 0 3) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA1088 + difference 3 0) (sourceB1088 + difference 0 3) sourceC1088) = raw9985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw9985; decide +kernel
    rw [ha]
    exact (canonical9985 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1088 + difference 3 1) (sourceB1088 + difference 1 3) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA1088 + difference 3 1) (sourceB1088 + difference 1 3) sourceC1088) = raw18148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18148; decide +kernel
    rw [ha]
    exact (canonical18148 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1088 + difference 3 2) (sourceB1088 + difference 2 3) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1088 + difference 3 2) (sourceB1088 + difference 2 3) sourceC1088) = raw18149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18149; decide +kernel
    rw [ha]
    exact (canonical18149 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1088 + difference 3 4) (sourceB1088 + difference 4 3) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA1088 + difference 3 4) (sourceB1088 + difference 4 3) sourceC1088) = raw18150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18150; decide +kernel
    rw [ha]
    exact (canonical18150 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1088 + difference 3 5) (sourceB1088 + difference 5 3) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1088 + difference 3 5) (sourceB1088 + difference 5 3) sourceC1088) = raw18151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18151; decide +kernel
    rw [ha]
    exact (canonical18151 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1088 + difference 4 0) (sourceB1088 + difference 0 4) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA1088 + difference 4 0) (sourceB1088 + difference 0 4) sourceC1088) = raw9990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw9990; decide +kernel
    rw [ha]
    exact (canonical9990 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1088 + difference 4 1) (sourceB1088 + difference 1 4) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA1088 + difference 4 1) (sourceB1088 + difference 1 4) sourceC1088) = raw18152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18152; decide +kernel
    rw [ha]
    exact (canonical18152 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1088 + difference 4 2) (sourceB1088 + difference 2 4) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA1088 + difference 4 2) (sourceB1088 + difference 2 4) sourceC1088) = raw18153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18153; decide +kernel
    rw [ha]
    exact (canonical18153 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1088 + difference 4 3) (sourceB1088 + difference 3 4) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1088 + difference 4 3) (sourceB1088 + difference 3 4) sourceC1088) = raw18154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18154; decide +kernel
    rw [ha]
    exact (canonical18154 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1088 + difference 4 5) (sourceB1088 + difference 5 4) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA1088 + difference 4 5) (sourceB1088 + difference 5 4) sourceC1088) = raw18155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18155; decide +kernel
    rw [ha]
    exact (canonical18155 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1088 + difference 5 0) (sourceB1088 + difference 0 5) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA1088 + difference 5 0) (sourceB1088 + difference 0 5) sourceC1088) = raw9995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw9995; decide +kernel
    rw [ha]
    exact (canonical9995 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1088 + difference 5 1) (sourceB1088 + difference 1 5) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA1088 + difference 5 1) (sourceB1088 + difference 1 5) sourceC1088) = raw18156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18156; decide +kernel
    rw [ha]
    exact (canonical18156 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1088 + difference 5 2) (sourceB1088 + difference 2 5) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA1088 + difference 5 2) (sourceB1088 + difference 2 5) sourceC1088) = raw18157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18157; decide +kernel
    rw [ha]
    exact (canonical18157 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1088 + difference 5 3) (sourceB1088 + difference 3 5) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA1088 + difference 5 3) (sourceB1088 + difference 3 5) sourceC1088) = raw18158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18158; decide +kernel
    rw [ha]
    exact (canonical18158 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1088 + difference 5 4) (sourceB1088 + difference 4 5) sourceC1088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA1088 + difference 5 4) (sourceB1088 + difference 4 5) sourceC1088) = raw18159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1088 sourceB1088 sourceC1088 difference raw18159; decide +kernel
    rw [ha]
    exact (canonical18159 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1088 sourceB1088 sourceC1088
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1088, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1089 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1089 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC1089 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceForm1089 : Integer.Sparse Master := [(Sum.inr 2676, 1), (Sum.inr 2677, 1), (Sum.inr 2678, 1), (Sum.inr 2681, 1), (Sum.inr 2773, 1), (Sum.inr 3524, 1), (Sum.inr 3530, 1), (Sum.inr 3533, 1), (Sum.inr 3538, 1), (Sum.inr 3557, 1), (Sum.inr 3564, 1), (Sum.inr 3570, 1), (Sum.inr 3582, 1), (Sum.inr 3799, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3834, 1), (Sum.inr 3837, 1), (Sum.inr 3846, 1), (Sum.inr 3850, 1), (Sum.inr 3852, 1), (Sum.inr 3854, 1), (Sum.inr 3860, 1), (Sum.inr 3870, 1), (Sum.inr 3871, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3886, 1), (Sum.inr 3888, 1), (Sum.inr 3995, 1)]

theorem sourceEq1089 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1089 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1089 + difference 0 1) (sourceB1089 + difference 1 0) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA1089 + difference 0 1) (sourceB1089 + difference 1 0) sourceC1089) = raw18160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18160; decide +kernel
    rw [ha]
    exact (canonical18160 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1089 + difference 0 2) (sourceB1089 + difference 2 0) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1089 + difference 0 2) (sourceB1089 + difference 2 0) sourceC1089) = raw18161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18161; decide +kernel
    rw [ha]
    exact (canonical18161 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1089 + difference 0 3) (sourceB1089 + difference 3 0) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1089 + difference 0 3) (sourceB1089 + difference 3 0) sourceC1089) = raw18162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18162; decide +kernel
    rw [ha]
    exact (canonical18162 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1089 + difference 0 4) (sourceB1089 + difference 4 0) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA1089 + difference 0 4) (sourceB1089 + difference 4 0) sourceC1089) = raw18163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18163; decide +kernel
    rw [ha]
    exact (canonical18163 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1089 + difference 0 5) (sourceB1089 + difference 5 0) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1089 + difference 0 5) (sourceB1089 + difference 5 0) sourceC1089) = raw18164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18164; decide +kernel
    rw [ha]
    exact (canonical18164 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1089 + difference 1 0) (sourceB1089 + difference 0 1) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA1089 + difference 1 0) (sourceB1089 + difference 0 1) sourceC1089) = raw18165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18165; decide +kernel
    rw [ha]
    exact (canonical18165 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1089 + difference 1 2) (sourceB1089 + difference 2 1) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA1089 + difference 1 2) (sourceB1089 + difference 2 1) sourceC1089) = raw10030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw10030; decide +kernel
    rw [ha]
    exact (canonical10030 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1089 + difference 1 3) (sourceB1089 + difference 3 1) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1089 + difference 1 3) (sourceB1089 + difference 3 1) sourceC1089) = raw10031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw10031; decide +kernel
    rw [ha]
    exact (canonical10031 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1089 + difference 1 4) (sourceB1089 + difference 4 1) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3860) := by
    have ha : (tripleCharges (sourceA1089 + difference 1 4) (sourceB1089 + difference 4 1) sourceC1089) = raw10032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw10032; decide +kernel
    rw [ha]
    exact (canonical10032 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1089 + difference 1 5) (sourceB1089 + difference 5 1) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1089 + difference 1 5) (sourceB1089 + difference 5 1) sourceC1089) = raw10033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw10033; decide +kernel
    rw [ha]
    exact (canonical10033 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1089 + difference 2 0) (sourceB1089 + difference 0 2) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA1089 + difference 2 0) (sourceB1089 + difference 0 2) sourceC1089) = raw10040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw10040; decide +kernel
    rw [ha]
    exact (canonical10040 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1089 + difference 2 1) (sourceB1089 + difference 1 2) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA1089 + difference 2 1) (sourceB1089 + difference 1 2) sourceC1089) = raw18166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18166; decide +kernel
    rw [ha]
    exact (canonical18166 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1089 + difference 2 3) (sourceB1089 + difference 3 2) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA1089 + difference 2 3) (sourceB1089 + difference 3 2) sourceC1089) = raw18167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18167; decide +kernel
    rw [ha]
    exact (canonical18167 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1089 + difference 2 4) (sourceB1089 + difference 4 2) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1089 + difference 2 4) (sourceB1089 + difference 4 2) sourceC1089) = raw18168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18168; decide +kernel
    rw [ha]
    exact (canonical18168 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1089 + difference 2 5) (sourceB1089 + difference 5 2) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA1089 + difference 2 5) (sourceB1089 + difference 5 2) sourceC1089) = raw18169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18169; decide +kernel
    rw [ha]
    exact (canonical18169 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1089 + difference 3 0) (sourceB1089 + difference 0 3) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA1089 + difference 3 0) (sourceB1089 + difference 0 3) sourceC1089) = raw10045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw10045; decide +kernel
    rw [ha]
    exact (canonical10045 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1089 + difference 3 1) (sourceB1089 + difference 1 3) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA1089 + difference 3 1) (sourceB1089 + difference 1 3) sourceC1089) = raw18170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18170; decide +kernel
    rw [ha]
    exact (canonical18170 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1089 + difference 3 2) (sourceB1089 + difference 2 3) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3870) := by
    have ha : (tripleCharges (sourceA1089 + difference 3 2) (sourceB1089 + difference 2 3) sourceC1089) = raw18171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18171; decide +kernel
    rw [ha]
    exact (canonical18171 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1089 + difference 3 4) (sourceB1089 + difference 4 3) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA1089 + difference 3 4) (sourceB1089 + difference 4 3) sourceC1089) = raw18172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18172; decide +kernel
    rw [ha]
    exact (canonical18172 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1089 + difference 3 5) (sourceB1089 + difference 5 3) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1089 + difference 3 5) (sourceB1089 + difference 5 3) sourceC1089) = raw18173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18173; decide +kernel
    rw [ha]
    exact (canonical18173 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1089 + difference 4 0) (sourceB1089 + difference 0 4) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA1089 + difference 4 0) (sourceB1089 + difference 0 4) sourceC1089) = raw10050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw10050; decide +kernel
    rw [ha]
    exact (canonical10050 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1089 + difference 4 1) (sourceB1089 + difference 1 4) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA1089 + difference 4 1) (sourceB1089 + difference 1 4) sourceC1089) = raw18174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18174; decide +kernel
    rw [ha]
    exact (canonical18174 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1089 + difference 4 2) (sourceB1089 + difference 2 4) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA1089 + difference 4 2) (sourceB1089 + difference 2 4) sourceC1089) = raw18175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18175; decide +kernel
    rw [ha]
    exact (canonical18175 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1089 + difference 4 3) (sourceB1089 + difference 3 4) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA1089 + difference 4 3) (sourceB1089 + difference 3 4) sourceC1089) = raw18176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18176; decide +kernel
    rw [ha]
    exact (canonical18176 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1089 + difference 4 5) (sourceB1089 + difference 5 4) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA1089 + difference 4 5) (sourceB1089 + difference 5 4) sourceC1089) = raw18177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18177; decide +kernel
    rw [ha]
    exact (canonical18177 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1089 + difference 5 0) (sourceB1089 + difference 0 5) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA1089 + difference 5 0) (sourceB1089 + difference 0 5) sourceC1089) = raw10055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw10055; decide +kernel
    rw [ha]
    exact (canonical10055 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1089 + difference 5 1) (sourceB1089 + difference 1 5) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA1089 + difference 5 1) (sourceB1089 + difference 1 5) sourceC1089) = raw18178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18178; decide +kernel
    rw [ha]
    exact (canonical18178 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1089 + difference 5 2) (sourceB1089 + difference 2 5) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA1089 + difference 5 2) (sourceB1089 + difference 2 5) sourceC1089) = raw18179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18179; decide +kernel
    rw [ha]
    exact (canonical18179 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1089 + difference 5 3) (sourceB1089 + difference 3 5) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA1089 + difference 5 3) (sourceB1089 + difference 3 5) sourceC1089) = raw18180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18180; decide +kernel
    rw [ha]
    exact (canonical18180 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1089 + difference 5 4) (sourceB1089 + difference 4 5) sourceC1089) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA1089 + difference 5 4) (sourceB1089 + difference 4 5) sourceC1089) = raw18181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1089 sourceB1089 sourceC1089 difference raw18181; decide +kernel
    rw [ha]
    exact (canonical18181 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1089 sourceB1089 sourceC1089
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1089, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1090 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1090 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC1090 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceForm1090 : Integer.Sparse Master := [(Sum.inr 4798, 2), (Sum.inr 4800, 1), (Sum.inr 4810, 2), (Sum.inr 4828, 2), (Sum.inr 4865, 2), (Sum.inr 5349, 2), (Sum.inr 5355, 2), (Sum.inr 5364, 1), (Sum.inr 5378, 2), (Sum.inr 5387, 2), (Sum.inr 5400, 2), (Sum.inr 5431, 2), (Sum.inr 5432, 1), (Sum.inr 5435, 2), (Sum.inr 5438, 2), (Sum.inr 5450, 2), (Sum.inr 5490, 1)]

theorem sourceEq1090 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1090 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1090 + difference 0 1) (sourceB1090 + difference 1 0) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1090 + difference 0 1) (sourceB1090 + difference 1 0) sourceC1090) = raw18182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18182; decide +kernel
    rw [ha]
    exact (canonical18182 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1090 + difference 0 2) (sourceB1090 + difference 2 0) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1090 + difference 0 2) (sourceB1090 + difference 2 0) sourceC1090) = raw18183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18183; decide +kernel
    rw [ha]
    exact (canonical18183 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1090 + difference 0 3) (sourceB1090 + difference 3 0) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1090 + difference 0 3) (sourceB1090 + difference 3 0) sourceC1090) = raw18184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18184; decide +kernel
    rw [ha]
    exact (canonical18184 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1090 + difference 0 4) (sourceB1090 + difference 4 0) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1090 + difference 0 4) (sourceB1090 + difference 4 0) sourceC1090) = raw18185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18185; decide +kernel
    rw [ha]
    exact (canonical18185 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1090 + difference 0 5) (sourceB1090 + difference 5 0) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1090 + difference 0 5) (sourceB1090 + difference 5 0) sourceC1090) = raw18186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18186; decide +kernel
    rw [ha]
    exact (canonical18186 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1090 + difference 1 0) (sourceB1090 + difference 0 1) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA1090 + difference 1 0) (sourceB1090 + difference 0 1) sourceC1090) = raw18187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18187; decide +kernel
    rw [ha]
    exact (canonical18187 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1090 + difference 1 2) (sourceB1090 + difference 2 1) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1090 + difference 1 2) (sourceB1090 + difference 2 1) sourceC1090) = raw18188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18188; decide +kernel
    rw [ha]
    exact (canonical18188 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1090 + difference 1 3) (sourceB1090 + difference 3 1) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA1090 + difference 1 3) (sourceB1090 + difference 3 1) sourceC1090) = raw18189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18189; decide +kernel
    rw [ha]
    exact (canonical18189 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1090 + difference 1 4) (sourceB1090 + difference 4 1) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1090 + difference 1 4) (sourceB1090 + difference 4 1) sourceC1090) = raw18190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18190; decide +kernel
    rw [ha]
    exact (canonical18190 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1090 + difference 1 5) (sourceB1090 + difference 5 1) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1090 + difference 1 5) (sourceB1090 + difference 5 1) sourceC1090) = raw18191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18191; decide +kernel
    rw [ha]
    exact (canonical18191 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1090 + difference 2 0) (sourceB1090 + difference 0 2) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA1090 + difference 2 0) (sourceB1090 + difference 0 2) sourceC1090) = raw18192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18192; decide +kernel
    rw [ha]
    exact (canonical18192 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1090 + difference 2 1) (sourceB1090 + difference 1 2) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1090 + difference 2 1) (sourceB1090 + difference 1 2) sourceC1090) = raw18193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18193; decide +kernel
    rw [ha]
    exact (canonical18193 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1090 + difference 2 3) (sourceB1090 + difference 3 2) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1090 + difference 2 3) (sourceB1090 + difference 3 2) sourceC1090) = raw18194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18194; decide +kernel
    rw [ha]
    exact (canonical18194 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1090 + difference 2 4) (sourceB1090 + difference 4 2) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1090 + difference 2 4) (sourceB1090 + difference 4 2) sourceC1090) = raw18195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18195; decide +kernel
    rw [ha]
    exact (canonical18195 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1090 + difference 2 5) (sourceB1090 + difference 5 2) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1090 + difference 2 5) (sourceB1090 + difference 5 2) sourceC1090) = raw18196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18196; decide +kernel
    rw [ha]
    exact (canonical18196 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1090 + difference 3 0) (sourceB1090 + difference 0 3) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA1090 + difference 3 0) (sourceB1090 + difference 0 3) sourceC1090) = raw18197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18197; decide +kernel
    rw [ha]
    exact (canonical18197 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1090 + difference 3 1) (sourceB1090 + difference 1 3) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1090 + difference 3 1) (sourceB1090 + difference 1 3) sourceC1090) = raw18198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18198; decide +kernel
    rw [ha]
    exact (canonical18198 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1090 + difference 3 2) (sourceB1090 + difference 2 3) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1090 + difference 3 2) (sourceB1090 + difference 2 3) sourceC1090) = raw18199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18199; decide +kernel
    rw [ha]
    exact (canonical18199 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1090 + difference 3 4) (sourceB1090 + difference 4 3) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1090 + difference 3 4) (sourceB1090 + difference 4 3) sourceC1090) = raw18200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18200; decide +kernel
    rw [ha]
    exact (canonical18200 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1090 + difference 3 5) (sourceB1090 + difference 5 3) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1090 + difference 3 5) (sourceB1090 + difference 5 3) sourceC1090) = raw18201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18201; decide +kernel
    rw [ha]
    exact (canonical18201 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1090 + difference 4 0) (sourceB1090 + difference 0 4) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA1090 + difference 4 0) (sourceB1090 + difference 0 4) sourceC1090) = raw18202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18202; decide +kernel
    rw [ha]
    exact (canonical18202 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1090 + difference 4 1) (sourceB1090 + difference 1 4) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA1090 + difference 4 1) (sourceB1090 + difference 1 4) sourceC1090) = raw18203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18203; decide +kernel
    rw [ha]
    exact (canonical18203 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1090 + difference 4 2) (sourceB1090 + difference 2 4) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1090 + difference 4 2) (sourceB1090 + difference 2 4) sourceC1090) = raw18204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18204; decide +kernel
    rw [ha]
    exact (canonical18204 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1090 + difference 4 3) (sourceB1090 + difference 3 4) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5364) := by
    have ha : (tripleCharges (sourceA1090 + difference 4 3) (sourceB1090 + difference 3 4) sourceC1090) = raw18205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18205; decide +kernel
    rw [ha]
    exact (canonical18205 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1090 + difference 4 5) (sourceB1090 + difference 5 4) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1090 + difference 4 5) (sourceB1090 + difference 5 4) sourceC1090) = raw18206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18206; decide +kernel
    rw [ha]
    exact (canonical18206 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1090 + difference 5 0) (sourceB1090 + difference 0 5) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA1090 + difference 5 0) (sourceB1090 + difference 0 5) sourceC1090) = raw18207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18207; decide +kernel
    rw [ha]
    exact (canonical18207 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1090 + difference 5 1) (sourceB1090 + difference 1 5) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA1090 + difference 5 1) (sourceB1090 + difference 1 5) sourceC1090) = raw18208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18208; decide +kernel
    rw [ha]
    exact (canonical18208 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1090 + difference 5 2) (sourceB1090 + difference 2 5) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA1090 + difference 5 2) (sourceB1090 + difference 2 5) sourceC1090) = raw18209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18209; decide +kernel
    rw [ha]
    exact (canonical18209 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1090 + difference 5 3) (sourceB1090 + difference 3 5) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA1090 + difference 5 3) (sourceB1090 + difference 3 5) sourceC1090) = raw18210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18210; decide +kernel
    rw [ha]
    exact (canonical18210 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1090 + difference 5 4) (sourceB1090 + difference 4 5) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA1090 + difference 5 4) (sourceB1090 + difference 4 5) sourceC1090) = raw18211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18211; decide +kernel
    rw [ha]
    exact (canonical18211 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1090 sourceB1090 sourceC1090
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1090, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1091 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1091 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC1091 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceForm1091 : Integer.Sparse Master := [(Sum.inr 5127, 1), (Sum.inr 5129, 2), (Sum.inr 5134, 2), (Sum.inr 5144, 2), (Sum.inr 5258, 2), (Sum.inr 5376, 1), (Sum.inr 5378, 2), (Sum.inr 5381, 2), (Sum.inr 5394, 1), (Sum.inr 5409, 2), (Sum.inr 5420, 1), (Sum.inr 5424, 2), (Sum.inr 5425, 2), (Sum.inr 5430, 2), (Sum.inr 5432, 2), (Sum.inr 5434, 2), (Sum.inr 5441, 1), (Sum.inr 5477, 1)]

theorem sourceEq1091 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1091 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1091 + difference 0 1) (sourceB1091 + difference 1 0) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1091 + difference 0 1) (sourceB1091 + difference 1 0) sourceC1091) = raw18212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18212; decide +kernel
    rw [ha]
    exact (canonical18212 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1091 + difference 0 2) (sourceB1091 + difference 2 0) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1091 + difference 0 2) (sourceB1091 + difference 2 0) sourceC1091) = raw18213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18213; decide +kernel
    rw [ha]
    exact (canonical18213 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1091 + difference 0 3) (sourceB1091 + difference 3 0) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1091 + difference 0 3) (sourceB1091 + difference 3 0) sourceC1091) = raw18214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18214; decide +kernel
    rw [ha]
    exact (canonical18214 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1091 + difference 0 4) (sourceB1091 + difference 4 0) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1091 + difference 0 4) (sourceB1091 + difference 4 0) sourceC1091) = raw18215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18215; decide +kernel
    rw [ha]
    exact (canonical18215 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1091 + difference 0 5) (sourceB1091 + difference 5 0) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1091 + difference 0 5) (sourceB1091 + difference 5 0) sourceC1091) = raw18216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18216; decide +kernel
    rw [ha]
    exact (canonical18216 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1091 + difference 1 0) (sourceB1091 + difference 0 1) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1091 + difference 1 0) (sourceB1091 + difference 0 1) sourceC1091) = raw12258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw12258; decide +kernel
    rw [ha]
    exact (canonical12258 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1091 + difference 1 2) (sourceB1091 + difference 2 1) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1091 + difference 1 2) (sourceB1091 + difference 2 1) sourceC1091) = raw18217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18217; decide +kernel
    rw [ha]
    exact (canonical18217 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1091 + difference 1 3) (sourceB1091 + difference 3 1) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1091 + difference 1 3) (sourceB1091 + difference 3 1) sourceC1091) = raw18218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18218; decide +kernel
    rw [ha]
    exact (canonical18218 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1091 + difference 1 4) (sourceB1091 + difference 4 1) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1091 + difference 1 4) (sourceB1091 + difference 4 1) sourceC1091) = raw18219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18219; decide +kernel
    rw [ha]
    exact (canonical18219 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1091 + difference 1 5) (sourceB1091 + difference 5 1) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1091 + difference 1 5) (sourceB1091 + difference 5 1) sourceC1091) = raw12232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw12232; decide +kernel
    rw [ha]
    exact (canonical12232 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1091 + difference 2 0) (sourceB1091 + difference 0 2) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1091 + difference 2 0) (sourceB1091 + difference 0 2) sourceC1091) = raw18220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18220; decide +kernel
    rw [ha]
    exact (canonical18220 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1091 + difference 2 1) (sourceB1091 + difference 1 2) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1091 + difference 2 1) (sourceB1091 + difference 1 2) sourceC1091) = raw18221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18221; decide +kernel
    rw [ha]
    exact (canonical18221 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1091 + difference 2 3) (sourceB1091 + difference 3 2) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA1091 + difference 2 3) (sourceB1091 + difference 3 2) sourceC1091) = raw18222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18222; decide +kernel
    rw [ha]
    exact (canonical18222 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1091 + difference 2 4) (sourceB1091 + difference 4 2) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1091 + difference 2 4) (sourceB1091 + difference 4 2) sourceC1091) = raw18223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18223; decide +kernel
    rw [ha]
    exact (canonical18223 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1091 + difference 2 5) (sourceB1091 + difference 5 2) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1091 + difference 2 5) (sourceB1091 + difference 5 2) sourceC1091) = raw18224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18224; decide +kernel
    rw [ha]
    exact (canonical18224 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1091 + difference 3 0) (sourceB1091 + difference 0 3) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA1091 + difference 3 0) (sourceB1091 + difference 0 3) sourceC1091) = raw12256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw12256; decide +kernel
    rw [ha]
    exact (canonical12256 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1091 + difference 3 1) (sourceB1091 + difference 1 3) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA1091 + difference 3 1) (sourceB1091 + difference 1 3) sourceC1091) = raw18225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18225; decide +kernel
    rw [ha]
    exact (canonical18225 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1091 + difference 3 2) (sourceB1091 + difference 2 3) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1091 + difference 3 2) (sourceB1091 + difference 2 3) sourceC1091) = raw18226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18226; decide +kernel
    rw [ha]
    exact (canonical18226 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1091 + difference 3 4) (sourceB1091 + difference 4 3) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1091 + difference 3 4) (sourceB1091 + difference 4 3) sourceC1091) = raw18227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18227; decide +kernel
    rw [ha]
    exact (canonical18227 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1091 + difference 3 5) (sourceB1091 + difference 5 3) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1091 + difference 3 5) (sourceB1091 + difference 5 3) sourceC1091) = raw12230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw12230; decide +kernel
    rw [ha]
    exact (canonical12230 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1091 + difference 4 0) (sourceB1091 + difference 0 4) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA1091 + difference 4 0) (sourceB1091 + difference 0 4) sourceC1091) = raw18228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18228; decide +kernel
    rw [ha]
    exact (canonical18228 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1091 + difference 4 1) (sourceB1091 + difference 1 4) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5376) := by
    have ha : (tripleCharges (sourceA1091 + difference 4 1) (sourceB1091 + difference 1 4) sourceC1091) = raw18229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18229; decide +kernel
    rw [ha]
    exact (canonical18229 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1091 + difference 4 2) (sourceB1091 + difference 2 4) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA1091 + difference 4 2) (sourceB1091 + difference 2 4) sourceC1091) = raw18230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18230; decide +kernel
    rw [ha]
    exact (canonical18230 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1091 + difference 4 3) (sourceB1091 + difference 3 4) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1091 + difference 4 3) (sourceB1091 + difference 3 4) sourceC1091) = raw18231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18231; decide +kernel
    rw [ha]
    exact (canonical18231 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1091 + difference 4 5) (sourceB1091 + difference 5 4) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1091 + difference 4 5) (sourceB1091 + difference 5 4) sourceC1091) = raw18232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18232; decide +kernel
    rw [ha]
    exact (canonical18232 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1091 + difference 5 0) (sourceB1091 + difference 0 5) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA1091 + difference 5 0) (sourceB1091 + difference 0 5) sourceC1091) = raw18233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18233; decide +kernel
    rw [ha]
    exact (canonical18233 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1091 + difference 5 1) (sourceB1091 + difference 1 5) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA1091 + difference 5 1) (sourceB1091 + difference 1 5) sourceC1091) = raw18234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18234; decide +kernel
    rw [ha]
    exact (canonical18234 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1091 + difference 5 2) (sourceB1091 + difference 2 5) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA1091 + difference 5 2) (sourceB1091 + difference 2 5) sourceC1091) = raw18235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18235; decide +kernel
    rw [ha]
    exact (canonical18235 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1091 + difference 5 3) (sourceB1091 + difference 3 5) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1091 + difference 5 3) (sourceB1091 + difference 3 5) sourceC1091) = raw18236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18236; decide +kernel
    rw [ha]
    exact (canonical18236 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1091 + difference 5 4) (sourceB1091 + difference 4 5) sourceC1091) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1091 + difference 5 4) (sourceB1091 + difference 4 5) sourceC1091) = raw18237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1091 sourceB1091 sourceC1091 difference raw18237; decide +kernel
    rw [ha]
    exact (canonical18237 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1091 sourceB1091 sourceC1091
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1091, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1092 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1092 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC1092 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceForm1092 : Integer.Sparse Master := [(Sum.inr 3513, 1), (Sum.inr 3514, 2), (Sum.inr 3516, 2), (Sum.inr 3533, 2), (Sum.inr 3557, 2), (Sum.inr 3793, 1), (Sum.inr 3795, 2), (Sum.inr 3807, 2), (Sum.inr 3833, 1), (Sum.inr 3834, 2), (Sum.inr 3838, 2), (Sum.inr 3840, 2), (Sum.inr 3850, 2), (Sum.inr 3852, 2), (Sum.inr 3860, 1), (Sum.inr 3870, 1), (Sum.inr 3871, 2), (Sum.inr 3989, 1)]

theorem sourceEq1092 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1092 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1092 + difference 0 1) (sourceB1092 + difference 1 0) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1092 + difference 0 1) (sourceB1092 + difference 1 0) sourceC1092) = raw18238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18238; decide +kernel
    rw [ha]
    exact (canonical18238 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1092 + difference 0 2) (sourceB1092 + difference 2 0) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1092 + difference 0 2) (sourceB1092 + difference 2 0) sourceC1092) = raw18239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18239; decide +kernel
    rw [ha]
    exact (canonical18239 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1092 + difference 0 3) (sourceB1092 + difference 3 0) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1092 + difference 0 3) (sourceB1092 + difference 3 0) sourceC1092) = raw18240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18240; decide +kernel
    rw [ha]
    exact (canonical18240 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1092 + difference 0 4) (sourceB1092 + difference 4 0) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1092 + difference 0 4) (sourceB1092 + difference 4 0) sourceC1092) = raw18241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18241; decide +kernel
    rw [ha]
    exact (canonical18241 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1092 + difference 0 5) (sourceB1092 + difference 5 0) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3989) := by
    have ha : (tripleCharges (sourceA1092 + difference 0 5) (sourceB1092 + difference 5 0) sourceC1092) = raw18242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18242; decide +kernel
    rw [ha]
    exact (canonical18242 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1092 + difference 1 0) (sourceB1092 + difference 0 1) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA1092 + difference 1 0) (sourceB1092 + difference 0 1) sourceC1092) = raw12318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw12318; decide +kernel
    rw [ha]
    exact (canonical12318 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1092 + difference 1 2) (sourceB1092 + difference 2 1) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1092 + difference 1 2) (sourceB1092 + difference 2 1) sourceC1092) = raw18243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18243; decide +kernel
    rw [ha]
    exact (canonical18243 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1092 + difference 1 3) (sourceB1092 + difference 3 1) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1092 + difference 1 3) (sourceB1092 + difference 3 1) sourceC1092) = raw18244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18244; decide +kernel
    rw [ha]
    exact (canonical18244 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1092 + difference 1 4) (sourceB1092 + difference 4 1) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3860) := by
    have ha : (tripleCharges (sourceA1092 + difference 1 4) (sourceB1092 + difference 4 1) sourceC1092) = raw18245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18245; decide +kernel
    rw [ha]
    exact (canonical18245 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1092 + difference 1 5) (sourceB1092 + difference 5 1) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1092 + difference 1 5) (sourceB1092 + difference 5 1) sourceC1092) = raw12292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw12292; decide +kernel
    rw [ha]
    exact (canonical12292 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1092 + difference 2 0) (sourceB1092 + difference 0 2) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA1092 + difference 2 0) (sourceB1092 + difference 0 2) sourceC1092) = raw18246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18246; decide +kernel
    rw [ha]
    exact (canonical18246 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1092 + difference 2 1) (sourceB1092 + difference 1 2) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA1092 + difference 2 1) (sourceB1092 + difference 1 2) sourceC1092) = raw18247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18247; decide +kernel
    rw [ha]
    exact (canonical18247 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1092 + difference 2 3) (sourceB1092 + difference 3 2) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA1092 + difference 2 3) (sourceB1092 + difference 3 2) sourceC1092) = raw18248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18248; decide +kernel
    rw [ha]
    exact (canonical18248 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1092 + difference 2 4) (sourceB1092 + difference 4 2) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1092 + difference 2 4) (sourceB1092 + difference 4 2) sourceC1092) = raw18249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18249; decide +kernel
    rw [ha]
    exact (canonical18249 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1092 + difference 2 5) (sourceB1092 + difference 5 2) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1092 + difference 2 5) (sourceB1092 + difference 5 2) sourceC1092) = raw18250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18250; decide +kernel
    rw [ha]
    exact (canonical18250 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1092 + difference 3 0) (sourceB1092 + difference 0 3) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA1092 + difference 3 0) (sourceB1092 + difference 0 3) sourceC1092) = raw12316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw12316; decide +kernel
    rw [ha]
    exact (canonical12316 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1092 + difference 3 1) (sourceB1092 + difference 1 3) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA1092 + difference 3 1) (sourceB1092 + difference 1 3) sourceC1092) = raw18251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18251; decide +kernel
    rw [ha]
    exact (canonical18251 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1092 + difference 3 2) (sourceB1092 + difference 2 3) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3870) := by
    have ha : (tripleCharges (sourceA1092 + difference 3 2) (sourceB1092 + difference 2 3) sourceC1092) = raw18252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18252; decide +kernel
    rw [ha]
    exact (canonical18252 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1092 + difference 3 4) (sourceB1092 + difference 4 3) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1092 + difference 3 4) (sourceB1092 + difference 4 3) sourceC1092) = raw18253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18253; decide +kernel
    rw [ha]
    exact (canonical18253 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1092 + difference 3 5) (sourceB1092 + difference 5 3) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1092 + difference 3 5) (sourceB1092 + difference 5 3) sourceC1092) = raw12290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw12290; decide +kernel
    rw [ha]
    exact (canonical12290 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1092 + difference 4 0) (sourceB1092 + difference 0 4) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA1092 + difference 4 0) (sourceB1092 + difference 0 4) sourceC1092) = raw18254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18254; decide +kernel
    rw [ha]
    exact (canonical18254 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1092 + difference 4 1) (sourceB1092 + difference 1 4) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3833) := by
    have ha : (tripleCharges (sourceA1092 + difference 4 1) (sourceB1092 + difference 1 4) sourceC1092) = raw18255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18255; decide +kernel
    rw [ha]
    exact (canonical18255 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1092 + difference 4 2) (sourceB1092 + difference 2 4) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA1092 + difference 4 2) (sourceB1092 + difference 2 4) sourceC1092) = raw18256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18256; decide +kernel
    rw [ha]
    exact (canonical18256 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1092 + difference 4 3) (sourceB1092 + difference 3 4) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA1092 + difference 4 3) (sourceB1092 + difference 3 4) sourceC1092) = raw18257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18257; decide +kernel
    rw [ha]
    exact (canonical18257 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1092 + difference 4 5) (sourceB1092 + difference 5 4) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1092 + difference 4 5) (sourceB1092 + difference 5 4) sourceC1092) = raw18258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18258; decide +kernel
    rw [ha]
    exact (canonical18258 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1092 + difference 5 0) (sourceB1092 + difference 0 5) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA1092 + difference 5 0) (sourceB1092 + difference 0 5) sourceC1092) = raw18259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18259; decide +kernel
    rw [ha]
    exact (canonical18259 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1092 + difference 5 1) (sourceB1092 + difference 1 5) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA1092 + difference 5 1) (sourceB1092 + difference 1 5) sourceC1092) = raw18260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18260; decide +kernel
    rw [ha]
    exact (canonical18260 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1092 + difference 5 2) (sourceB1092 + difference 2 5) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA1092 + difference 5 2) (sourceB1092 + difference 2 5) sourceC1092) = raw18261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18261; decide +kernel
    rw [ha]
    exact (canonical18261 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1092 + difference 5 3) (sourceB1092 + difference 3 5) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA1092 + difference 5 3) (sourceB1092 + difference 3 5) sourceC1092) = raw18262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18262; decide +kernel
    rw [ha]
    exact (canonical18262 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1092 + difference 5 4) (sourceB1092 + difference 4 5) sourceC1092) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA1092 + difference 5 4) (sourceB1092 + difference 4 5) sourceC1092) = raw18263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1092 sourceB1092 sourceC1092 difference raw18263; decide +kernel
    rw [ha]
    exact (canonical18263 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1092 sourceB1092 sourceC1092
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1092, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1093 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1093 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC1093 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceForm1093 : Integer.Sparse Master := [(Sum.inr 4778, 1), (Sum.inr 4782, 4), (Sum.inr 4801, 4), (Sum.inr 5341, 2), (Sum.inr 5344, 2), (Sum.inr 5351, 4), (Sum.inr 5415, 2), (Sum.inr 5423, 2), (Sum.inr 5424, 4), (Sum.inr 5433, 4), (Sum.inr 5500, 1)]

theorem sourceEq1093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1093 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1093 + difference 0 1) (sourceB1093 + difference 1 0) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1093 + difference 0 1) (sourceB1093 + difference 1 0) sourceC1093) = raw18264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18264; decide +kernel
    rw [ha]
    exact (canonical18264 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1093 + difference 0 2) (sourceB1093 + difference 2 0) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1093 + difference 0 2) (sourceB1093 + difference 2 0) sourceC1093) = raw18265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18265; decide +kernel
    rw [ha]
    exact (canonical18265 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1093 + difference 0 3) (sourceB1093 + difference 3 0) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1093 + difference 0 3) (sourceB1093 + difference 3 0) sourceC1093) = raw18266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18266; decide +kernel
    rw [ha]
    exact (canonical18266 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1093 + difference 0 4) (sourceB1093 + difference 4 0) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1093 + difference 0 4) (sourceB1093 + difference 4 0) sourceC1093) = raw18267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18267; decide +kernel
    rw [ha]
    exact (canonical18267 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1093 + difference 0 5) (sourceB1093 + difference 5 0) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA1093 + difference 0 5) (sourceB1093 + difference 5 0) sourceC1093) = raw18268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18268; decide +kernel
    rw [ha]
    exact (canonical18268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1093 + difference 1 0) (sourceB1093 + difference 0 1) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA1093 + difference 1 0) (sourceB1093 + difference 0 1) sourceC1093) = raw18269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18269; decide +kernel
    rw [ha]
    exact (canonical18269 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1093 + difference 1 2) (sourceB1093 + difference 2 1) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1093 + difference 1 2) (sourceB1093 + difference 2 1) sourceC1093) = raw18270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18270; decide +kernel
    rw [ha]
    exact (canonical18270 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1093 + difference 1 3) (sourceB1093 + difference 3 1) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1093 + difference 1 3) (sourceB1093 + difference 3 1) sourceC1093) = raw18271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18271; decide +kernel
    rw [ha]
    exact (canonical18271 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1093 + difference 1 4) (sourceB1093 + difference 4 1) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA1093 + difference 1 4) (sourceB1093 + difference 4 1) sourceC1093) = raw18272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18272; decide +kernel
    rw [ha]
    exact (canonical18272 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1093 + difference 1 5) (sourceB1093 + difference 5 1) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1093 + difference 1 5) (sourceB1093 + difference 5 1) sourceC1093) = raw18273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18273; decide +kernel
    rw [ha]
    exact (canonical18273 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1093 + difference 2 0) (sourceB1093 + difference 0 2) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA1093 + difference 2 0) (sourceB1093 + difference 0 2) sourceC1093) = raw18274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18274; decide +kernel
    rw [ha]
    exact (canonical18274 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1093 + difference 2 1) (sourceB1093 + difference 1 2) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA1093 + difference 2 1) (sourceB1093 + difference 1 2) sourceC1093) = raw18275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18275; decide +kernel
    rw [ha]
    exact (canonical18275 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1093 + difference 2 3) (sourceB1093 + difference 3 2) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA1093 + difference 2 3) (sourceB1093 + difference 3 2) sourceC1093) = raw18276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18276; decide +kernel
    rw [ha]
    exact (canonical18276 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1093 + difference 2 4) (sourceB1093 + difference 4 2) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1093 + difference 2 4) (sourceB1093 + difference 4 2) sourceC1093) = raw18277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18277; decide +kernel
    rw [ha]
    exact (canonical18277 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1093 + difference 2 5) (sourceB1093 + difference 5 2) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1093 + difference 2 5) (sourceB1093 + difference 5 2) sourceC1093) = raw18278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18278; decide +kernel
    rw [ha]
    exact (canonical18278 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1093 + difference 3 0) (sourceB1093 + difference 0 3) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA1093 + difference 3 0) (sourceB1093 + difference 0 3) sourceC1093) = raw18279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18279; decide +kernel
    rw [ha]
    exact (canonical18279 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1093 + difference 3 1) (sourceB1093 + difference 1 3) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1093 + difference 3 1) (sourceB1093 + difference 1 3) sourceC1093) = raw18280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18280; decide +kernel
    rw [ha]
    exact (canonical18280 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1093 + difference 3 2) (sourceB1093 + difference 2 3) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA1093 + difference 3 2) (sourceB1093 + difference 2 3) sourceC1093) = raw18281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18281; decide +kernel
    rw [ha]
    exact (canonical18281 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1093 + difference 3 4) (sourceB1093 + difference 4 3) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1093 + difference 3 4) (sourceB1093 + difference 4 3) sourceC1093) = raw18282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18282; decide +kernel
    rw [ha]
    exact (canonical18282 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1093 + difference 3 5) (sourceB1093 + difference 5 3) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1093 + difference 3 5) (sourceB1093 + difference 5 3) sourceC1093) = raw18283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18283; decide +kernel
    rw [ha]
    exact (canonical18283 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1093 + difference 4 0) (sourceB1093 + difference 0 4) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA1093 + difference 4 0) (sourceB1093 + difference 0 4) sourceC1093) = raw18284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18284; decide +kernel
    rw [ha]
    exact (canonical18284 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1093 + difference 4 1) (sourceB1093 + difference 1 4) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA1093 + difference 4 1) (sourceB1093 + difference 1 4) sourceC1093) = raw18285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18285; decide +kernel
    rw [ha]
    exact (canonical18285 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1093 + difference 4 2) (sourceB1093 + difference 2 4) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1093 + difference 4 2) (sourceB1093 + difference 2 4) sourceC1093) = raw18286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18286; decide +kernel
    rw [ha]
    exact (canonical18286 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1093 + difference 4 3) (sourceB1093 + difference 3 4) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA1093 + difference 4 3) (sourceB1093 + difference 3 4) sourceC1093) = raw18287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18287; decide +kernel
    rw [ha]
    exact (canonical18287 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1093 + difference 4 5) (sourceB1093 + difference 5 4) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1093 + difference 4 5) (sourceB1093 + difference 5 4) sourceC1093) = raw18288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18288; decide +kernel
    rw [ha]
    exact (canonical18288 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1093 + difference 5 0) (sourceB1093 + difference 0 5) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4778) := by
    have ha : (tripleCharges (sourceA1093 + difference 5 0) (sourceB1093 + difference 0 5) sourceC1093) = raw18289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18289; decide +kernel
    rw [ha]
    exact (canonical18289 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1093 + difference 5 1) (sourceB1093 + difference 1 5) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA1093 + difference 5 1) (sourceB1093 + difference 1 5) sourceC1093) = raw18290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18290; decide +kernel
    rw [ha]
    exact (canonical18290 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1093 + difference 5 2) (sourceB1093 + difference 2 5) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA1093 + difference 5 2) (sourceB1093 + difference 2 5) sourceC1093) = raw18291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18291; decide +kernel
    rw [ha]
    exact (canonical18291 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1093 + difference 5 3) (sourceB1093 + difference 3 5) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA1093 + difference 5 3) (sourceB1093 + difference 3 5) sourceC1093) = raw18292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18292; decide +kernel
    rw [ha]
    exact (canonical18292 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1093 + difference 5 4) (sourceB1093 + difference 4 5) sourceC1093) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA1093 + difference 5 4) (sourceB1093 + difference 4 5) sourceC1093) = raw18293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1093 sourceB1093 sourceC1093 difference raw18293; decide +kernel
    rw [ha]
    exact (canonical18293 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1093 sourceB1093 sourceC1093
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1093, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1094 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1094 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC1094 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1094 : Integer.Sparse Master := [(Sum.inr 4094, 1), (Sum.inr 5168, 4), (Sum.inr 5171, 1), (Sum.inr 5176, 2), (Sum.inr 5308, 2), (Sum.inr 5387, 4), (Sum.inr 5389, 1), (Sum.inr 5415, 2), (Sum.inr 5439, 4), (Sum.inr 5441, 4), (Sum.inr 5443, 2), (Sum.inr 5455, 2), (Sum.inr 5491, 1)]

theorem sourceEq1094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1094 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1094 + difference 0 1) (sourceB1094 + difference 1 0) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1094 + difference 0 1) (sourceB1094 + difference 1 0) sourceC1094) = raw18294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18294; decide +kernel
    rw [ha]
    exact (canonical18294 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1094 + difference 0 2) (sourceB1094 + difference 2 0) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1094 + difference 0 2) (sourceB1094 + difference 2 0) sourceC1094) = raw18295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18295; decide +kernel
    rw [ha]
    exact (canonical18295 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1094 + difference 0 3) (sourceB1094 + difference 3 0) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1094 + difference 0 3) (sourceB1094 + difference 3 0) sourceC1094) = raw18296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18296; decide +kernel
    rw [ha]
    exact (canonical18296 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1094 + difference 0 4) (sourceB1094 + difference 4 0) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA1094 + difference 0 4) (sourceB1094 + difference 4 0) sourceC1094) = raw18297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18297; decide +kernel
    rw [ha]
    exact (canonical18297 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1094 + difference 0 5) (sourceB1094 + difference 5 0) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1094 + difference 0 5) (sourceB1094 + difference 5 0) sourceC1094) = raw18298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18298; decide +kernel
    rw [ha]
    exact (canonical18298 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1094 + difference 1 0) (sourceB1094 + difference 0 1) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA1094 + difference 1 0) (sourceB1094 + difference 0 1) sourceC1094) = raw5082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw5082; decide +kernel
    rw [ha]
    exact (canonical5082 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1094 + difference 1 2) (sourceB1094 + difference 2 1) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1094 + difference 1 2) (sourceB1094 + difference 2 1) sourceC1094) = raw10217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw10217; decide +kernel
    rw [ha]
    exact (canonical10217 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1094 + difference 1 3) (sourceB1094 + difference 3 1) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1094 + difference 1 3) (sourceB1094 + difference 3 1) sourceC1094) = raw10218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw10218; decide +kernel
    rw [ha]
    exact (canonical10218 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1094 + difference 1 4) (sourceB1094 + difference 4 1) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA1094 + difference 1 4) (sourceB1094 + difference 4 1) sourceC1094) = raw5062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw5062; decide +kernel
    rw [ha]
    exact (canonical5062 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1094 + difference 1 5) (sourceB1094 + difference 5 1) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA1094 + difference 1 5) (sourceB1094 + difference 5 1) sourceC1094) = raw10219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw10219; decide +kernel
    rw [ha]
    exact (canonical10219 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1094 + difference 2 0) (sourceB1094 + difference 0 2) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1094 + difference 2 0) (sourceB1094 + difference 0 2) sourceC1094) = raw10225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw10225; decide +kernel
    rw [ha]
    exact (canonical10225 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1094 + difference 2 1) (sourceB1094 + difference 1 2) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1094 + difference 2 1) (sourceB1094 + difference 1 2) sourceC1094) = raw18299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18299; decide +kernel
    rw [ha]
    exact (canonical18299 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1094 + difference 2 3) (sourceB1094 + difference 3 2) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA1094 + difference 2 3) (sourceB1094 + difference 3 2) sourceC1094) = raw18300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18300; decide +kernel
    rw [ha]
    exact (canonical18300 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1094 + difference 2 4) (sourceB1094 + difference 4 2) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1094 + difference 2 4) (sourceB1094 + difference 4 2) sourceC1094) = raw18301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18301; decide +kernel
    rw [ha]
    exact (canonical18301 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1094 + difference 2 5) (sourceB1094 + difference 5 2) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1094 + difference 2 5) (sourceB1094 + difference 5 2) sourceC1094) = raw18302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18302; decide +kernel
    rw [ha]
    exact (canonical18302 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1094 + difference 3 0) (sourceB1094 + difference 0 3) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1094 + difference 3 0) (sourceB1094 + difference 0 3) sourceC1094) = raw10229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw10229; decide +kernel
    rw [ha]
    exact (canonical10229 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1094 + difference 3 1) (sourceB1094 + difference 1 3) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1094 + difference 3 1) (sourceB1094 + difference 1 3) sourceC1094) = raw18303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18303; decide +kernel
    rw [ha]
    exact (canonical18303 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1094 + difference 3 2) (sourceB1094 + difference 2 3) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA1094 + difference 3 2) (sourceB1094 + difference 2 3) sourceC1094) = raw18304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18304; decide +kernel
    rw [ha]
    exact (canonical18304 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1094 + difference 3 4) (sourceB1094 + difference 4 3) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1094 + difference 3 4) (sourceB1094 + difference 4 3) sourceC1094) = raw18305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18305; decide +kernel
    rw [ha]
    exact (canonical18305 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1094 + difference 3 5) (sourceB1094 + difference 5 3) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1094 + difference 3 5) (sourceB1094 + difference 5 3) sourceC1094) = raw12080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw12080; decide +kernel
    rw [ha]
    exact (canonical12080 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1094 + difference 4 0) (sourceB1094 + difference 0 4) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1094 + difference 4 0) (sourceB1094 + difference 0 4) sourceC1094) = raw10233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw10233; decide +kernel
    rw [ha]
    exact (canonical10233 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1094 + difference 4 1) (sourceB1094 + difference 1 4) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA1094 + difference 4 1) (sourceB1094 + difference 1 4) sourceC1094) = raw18306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18306; decide +kernel
    rw [ha]
    exact (canonical18306 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1094 + difference 4 2) (sourceB1094 + difference 2 4) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1094 + difference 4 2) (sourceB1094 + difference 2 4) sourceC1094) = raw18307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18307; decide +kernel
    rw [ha]
    exact (canonical18307 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1094 + difference 4 3) (sourceB1094 + difference 3 4) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1094 + difference 4 3) (sourceB1094 + difference 3 4) sourceC1094) = raw18308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18308; decide +kernel
    rw [ha]
    exact (canonical18308 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1094 + difference 4 5) (sourceB1094 + difference 5 4) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1094 + difference 4 5) (sourceB1094 + difference 5 4) sourceC1094) = raw18309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18309; decide +kernel
    rw [ha]
    exact (canonical18309 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1094 + difference 5 0) (sourceB1094 + difference 0 5) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1094 + difference 5 0) (sourceB1094 + difference 0 5) sourceC1094) = raw5079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw5079; decide +kernel
    rw [ha]
    exact (canonical5079 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1094 + difference 5 1) (sourceB1094 + difference 1 5) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1094 + difference 5 1) (sourceB1094 + difference 1 5) sourceC1094) = raw18310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18310; decide +kernel
    rw [ha]
    exact (canonical18310 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1094 + difference 5 2) (sourceB1094 + difference 2 5) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1094 + difference 5 2) (sourceB1094 + difference 2 5) sourceC1094) = raw18311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18311; decide +kernel
    rw [ha]
    exact (canonical18311 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1094 + difference 5 3) (sourceB1094 + difference 3 5) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1094 + difference 5 3) (sourceB1094 + difference 3 5) sourceC1094) = raw18312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw18312; decide +kernel
    rw [ha]
    exact (canonical18312 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1094 + difference 5 4) (sourceB1094 + difference 4 5) sourceC1094) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA1094 + difference 5 4) (sourceB1094 + difference 4 5) sourceC1094) = raw5058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1094 sourceB1094 sourceC1094 difference raw5058; decide +kernel
    rw [ha]
    exact (canonical5058 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1094 sourceB1094 sourceC1094
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1094, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1095 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1095 : Charge := ![0, 1, 0, -1, 0, 0]
def sourceC1095 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm1095 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 5072, 1), (Sum.inr 5075, 1), (Sum.inr 5080, 1), (Sum.inr 5101, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5163, 1), (Sum.inr 5258, 1), (Sum.inr 5274, 1), (Sum.inr 5351, 1), (Sum.inr 5355, 1), (Sum.inr 5367, 1), (Sum.inr 5378, 1), (Sum.inr 5384, 1), (Sum.inr 5394, 1), (Sum.inr 5400, 1), (Sum.inr 5405, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5428, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5438, 1), (Sum.inr 5441, 1), (Sum.inr 5442, 1), (Sum.inr 5483, 1)]

theorem sourceEq1095 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1095 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1095 + difference 0 1) (sourceB1095 + difference 1 0) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1095 + difference 0 1) (sourceB1095 + difference 1 0) sourceC1095) = raw18313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18313; decide +kernel
    rw [ha]
    exact (canonical18313 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1095 + difference 0 2) (sourceB1095 + difference 2 0) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1095 + difference 0 2) (sourceB1095 + difference 2 0) sourceC1095) = raw18314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18314; decide +kernel
    rw [ha]
    exact (canonical18314 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1095 + difference 0 3) (sourceB1095 + difference 3 0) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1095 + difference 0 3) (sourceB1095 + difference 3 0) sourceC1095) = raw18315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18315; decide +kernel
    rw [ha]
    exact (canonical18315 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1095 + difference 0 4) (sourceB1095 + difference 4 0) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1095 + difference 0 4) (sourceB1095 + difference 4 0) sourceC1095) = raw18316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18316; decide +kernel
    rw [ha]
    exact (canonical18316 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1095 + difference 0 5) (sourceB1095 + difference 5 0) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1095 + difference 0 5) (sourceB1095 + difference 5 0) sourceC1095) = raw18317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18317; decide +kernel
    rw [ha]
    exact (canonical18317 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1095 + difference 1 0) (sourceB1095 + difference 0 1) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA1095 + difference 1 0) (sourceB1095 + difference 0 1) sourceC1095) = raw18318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18318; decide +kernel
    rw [ha]
    exact (canonical18318 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1095 + difference 1 2) (sourceB1095 + difference 2 1) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1095 + difference 1 2) (sourceB1095 + difference 2 1) sourceC1095) = raw10540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw10540; decide +kernel
    rw [ha]
    exact (canonical10540 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1095 + difference 1 3) (sourceB1095 + difference 3 1) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1095 + difference 1 3) (sourceB1095 + difference 3 1) sourceC1095) = raw10541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw10541; decide +kernel
    rw [ha]
    exact (canonical10541 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1095 + difference 1 4) (sourceB1095 + difference 4 1) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1095 + difference 1 4) (sourceB1095 + difference 4 1) sourceC1095) = raw10542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw10542; decide +kernel
    rw [ha]
    exact (canonical10542 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1095 + difference 1 5) (sourceB1095 + difference 5 1) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1095 + difference 1 5) (sourceB1095 + difference 5 1) sourceC1095) = raw10543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw10543; decide +kernel
    rw [ha]
    exact (canonical10543 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1095 + difference 2 0) (sourceB1095 + difference 0 2) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1095 + difference 2 0) (sourceB1095 + difference 0 2) sourceC1095) = raw10550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw10550; decide +kernel
    rw [ha]
    exact (canonical10550 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1095 + difference 2 1) (sourceB1095 + difference 1 2) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1095 + difference 2 1) (sourceB1095 + difference 1 2) sourceC1095) = raw18319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18319; decide +kernel
    rw [ha]
    exact (canonical18319 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1095 + difference 2 3) (sourceB1095 + difference 3 2) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA1095 + difference 2 3) (sourceB1095 + difference 3 2) sourceC1095) = raw18320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18320; decide +kernel
    rw [ha]
    exact (canonical18320 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1095 + difference 2 4) (sourceB1095 + difference 4 2) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1095 + difference 2 4) (sourceB1095 + difference 4 2) sourceC1095) = raw18321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18321; decide +kernel
    rw [ha]
    exact (canonical18321 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1095 + difference 2 5) (sourceB1095 + difference 5 2) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1095 + difference 2 5) (sourceB1095 + difference 5 2) sourceC1095) = raw18322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18322; decide +kernel
    rw [ha]
    exact (canonical18322 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1095 + difference 3 0) (sourceB1095 + difference 0 3) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA1095 + difference 3 0) (sourceB1095 + difference 0 3) sourceC1095) = raw10555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw10555; decide +kernel
    rw [ha]
    exact (canonical10555 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1095 + difference 3 1) (sourceB1095 + difference 1 3) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1095 + difference 3 1) (sourceB1095 + difference 1 3) sourceC1095) = raw18323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18323; decide +kernel
    rw [ha]
    exact (canonical18323 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1095 + difference 3 2) (sourceB1095 + difference 2 3) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1095 + difference 3 2) (sourceB1095 + difference 2 3) sourceC1095) = raw18324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18324; decide +kernel
    rw [ha]
    exact (canonical18324 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1095 + difference 3 4) (sourceB1095 + difference 4 3) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1095 + difference 3 4) (sourceB1095 + difference 4 3) sourceC1095) = raw18325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18325; decide +kernel
    rw [ha]
    exact (canonical18325 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1095 + difference 3 5) (sourceB1095 + difference 5 3) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1095 + difference 3 5) (sourceB1095 + difference 5 3) sourceC1095) = raw18326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18326; decide +kernel
    rw [ha]
    exact (canonical18326 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1095 + difference 4 0) (sourceB1095 + difference 0 4) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA1095 + difference 4 0) (sourceB1095 + difference 0 4) sourceC1095) = raw10560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw10560; decide +kernel
    rw [ha]
    exact (canonical10560 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1095 + difference 4 1) (sourceB1095 + difference 1 4) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA1095 + difference 4 1) (sourceB1095 + difference 1 4) sourceC1095) = raw18327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18327; decide +kernel
    rw [ha]
    exact (canonical18327 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1095 + difference 4 2) (sourceB1095 + difference 2 4) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1095 + difference 4 2) (sourceB1095 + difference 2 4) sourceC1095) = raw18328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18328; decide +kernel
    rw [ha]
    exact (canonical18328 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1095 + difference 4 3) (sourceB1095 + difference 3 4) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA1095 + difference 4 3) (sourceB1095 + difference 3 4) sourceC1095) = raw18329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18329; decide +kernel
    rw [ha]
    exact (canonical18329 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1095 + difference 4 5) (sourceB1095 + difference 5 4) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1095 + difference 4 5) (sourceB1095 + difference 5 4) sourceC1095) = raw18330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18330; decide +kernel
    rw [ha]
    exact (canonical18330 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1095 + difference 5 0) (sourceB1095 + difference 0 5) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1095 + difference 5 0) (sourceB1095 + difference 0 5) sourceC1095) = raw10565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw10565; decide +kernel
    rw [ha]
    exact (canonical10565 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1095 + difference 5 1) (sourceB1095 + difference 1 5) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA1095 + difference 5 1) (sourceB1095 + difference 1 5) sourceC1095) = raw18331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18331; decide +kernel
    rw [ha]
    exact (canonical18331 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1095 + difference 5 2) (sourceB1095 + difference 2 5) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA1095 + difference 5 2) (sourceB1095 + difference 2 5) sourceC1095) = raw18332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18332; decide +kernel
    rw [ha]
    exact (canonical18332 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1095 + difference 5 3) (sourceB1095 + difference 3 5) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA1095 + difference 5 3) (sourceB1095 + difference 3 5) sourceC1095) = raw18333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18333; decide +kernel
    rw [ha]
    exact (canonical18333 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1095 + difference 5 4) (sourceB1095 + difference 4 5) sourceC1095) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1095 + difference 5 4) (sourceB1095 + difference 4 5) sourceC1095) = raw18334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1095 sourceB1095 sourceC1095 difference raw18334; decide +kernel
    rw [ha]
    exact (canonical18334 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1095 sourceB1095 sourceC1095
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1095, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1096 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1096 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1096 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm1096 : Integer.Sparse Master := [(Sum.inr 4080, 4), (Sum.inr 4081, 1), (Sum.inr 4082, 2), (Sum.inr 4084, 2), (Sum.inr 4088, 4), (Sum.inr 4089, 1), (Sum.inr 4090, 2), (Sum.inr 4091, 4), (Sum.inr 4092, 6), (Sum.inr 4093, 2), (Sum.inr 4094, 1), (Sum.inr 4096, 1)]

theorem sourceEq1096 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1096 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1096 + difference 0 1) (sourceB1096 + difference 1 0) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1096 + difference 0 1) (sourceB1096 + difference 1 0) sourceC1096) = raw3448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw3448; decide +kernel
    rw [ha]
    exact (canonical3448 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1096 + difference 0 2) (sourceB1096 + difference 2 0) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1096 + difference 0 2) (sourceB1096 + difference 2 0) sourceC1096) = raw3449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw3449; decide +kernel
    rw [ha]
    exact (canonical3449 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1096 + difference 0 3) (sourceB1096 + difference 3 0) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1096 + difference 0 3) (sourceB1096 + difference 3 0) sourceC1096) = raw3450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw3450; decide +kernel
    rw [ha]
    exact (canonical3450 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1096 + difference 0 4) (sourceB1096 + difference 4 0) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA1096 + difference 0 4) (sourceB1096 + difference 4 0) sourceC1096) = raw2909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw2909; decide +kernel
    rw [ha]
    exact (canonical2909 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1096 + difference 0 5) (sourceB1096 + difference 5 0) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1096 + difference 0 5) (sourceB1096 + difference 5 0) sourceC1096) = raw3319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw3319; decide +kernel
    rw [ha]
    exact (canonical3319 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1096 + difference 1 0) (sourceB1096 + difference 0 1) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1096 + difference 1 0) (sourceB1096 + difference 0 1) sourceC1096) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1096 + difference 1 2) (sourceB1096 + difference 2 1) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1096 + difference 1 2) (sourceB1096 + difference 2 1) sourceC1096) = raw2931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw2931; decide +kernel
    rw [ha]
    exact (canonical2931 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1096 + difference 1 3) (sourceB1096 + difference 3 1) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1096 + difference 1 3) (sourceB1096 + difference 3 1) sourceC1096) = raw2932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw2932; decide +kernel
    rw [ha]
    exact (canonical2932 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1096 + difference 1 4) (sourceB1096 + difference 4 1) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA1096 + difference 1 4) (sourceB1096 + difference 4 1) sourceC1096) = raw3340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw3340; decide +kernel
    rw [ha]
    exact (canonical3340 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1096 + difference 1 5) (sourceB1096 + difference 5 1) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA1096 + difference 1 5) (sourceB1096 + difference 5 1) sourceC1096) = raw2933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw2933; decide +kernel
    rw [ha]
    exact (canonical2933 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1096 + difference 2 0) (sourceB1096 + difference 0 2) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1096 + difference 2 0) (sourceB1096 + difference 0 2) sourceC1096) = raw11535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw11535; decide +kernel
    rw [ha]
    exact (canonical11535 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1096 + difference 2 1) (sourceB1096 + difference 1 2) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA1096 + difference 2 1) (sourceB1096 + difference 1 2) sourceC1096) = raw18335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw18335; decide +kernel
    rw [ha]
    exact (canonical18335 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1096 + difference 2 3) (sourceB1096 + difference 3 2) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1096 + difference 2 3) (sourceB1096 + difference 3 2) sourceC1096) = raw18336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw18336; decide +kernel
    rw [ha]
    exact (canonical18336 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1096 + difference 2 4) (sourceB1096 + difference 4 2) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1096 + difference 2 4) (sourceB1096 + difference 4 2) sourceC1096) = raw2920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw2920; decide +kernel
    rw [ha]
    exact (canonical2920 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1096 + difference 2 5) (sourceB1096 + difference 5 2) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1096 + difference 2 5) (sourceB1096 + difference 5 2) sourceC1096) = raw3328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw3328; decide +kernel
    rw [ha]
    exact (canonical3328 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1096 + difference 3 0) (sourceB1096 + difference 0 3) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1096 + difference 3 0) (sourceB1096 + difference 0 3) sourceC1096) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1096 + difference 3 1) (sourceB1096 + difference 1 3) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA1096 + difference 3 1) (sourceB1096 + difference 1 3) sourceC1096) = raw18337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw18337; decide +kernel
    rw [ha]
    exact (canonical18337 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1096 + difference 3 2) (sourceB1096 + difference 2 3) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1096 + difference 3 2) (sourceB1096 + difference 2 3) sourceC1096) = raw18338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw18338; decide +kernel
    rw [ha]
    exact (canonical18338 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1096 + difference 3 4) (sourceB1096 + difference 4 3) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1096 + difference 3 4) (sourceB1096 + difference 4 3) sourceC1096) = raw2925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw2925; decide +kernel
    rw [ha]
    exact (canonical2925 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1096 + difference 3 5) (sourceB1096 + difference 5 3) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1096 + difference 3 5) (sourceB1096 + difference 5 3) sourceC1096) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1096 + difference 4 0) (sourceB1096 + difference 0 4) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA1096 + difference 4 0) (sourceB1096 + difference 0 4) sourceC1096) = raw11541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw11541; decide +kernel
    rw [ha]
    exact (canonical11541 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1096 + difference 4 1) (sourceB1096 + difference 1 4) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (tripleCharges (sourceA1096 + difference 4 1) (sourceB1096 + difference 1 4) sourceC1096) = raw18339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw18339; decide +kernel
    rw [ha]
    exact (canonical18339 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1096 + difference 4 2) (sourceB1096 + difference 2 4) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA1096 + difference 4 2) (sourceB1096 + difference 2 4) sourceC1096) = raw18340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw18340; decide +kernel
    rw [ha]
    exact (canonical18340 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1096 + difference 4 3) (sourceB1096 + difference 3 4) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA1096 + difference 4 3) (sourceB1096 + difference 3 4) sourceC1096) = raw18341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw18341; decide +kernel
    rw [ha]
    exact (canonical18341 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1096 + difference 4 5) (sourceB1096 + difference 5 4) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1096 + difference 4 5) (sourceB1096 + difference 5 4) sourceC1096) = raw3336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw3336; decide +kernel
    rw [ha]
    exact (canonical3336 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1096 + difference 5 0) (sourceB1096 + difference 0 5) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA1096 + difference 5 0) (sourceB1096 + difference 0 5) sourceC1096) = raw5210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw5210; decide +kernel
    rw [ha]
    exact (canonical5210 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1096 + difference 5 1) (sourceB1096 + difference 1 5) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA1096 + difference 5 1) (sourceB1096 + difference 1 5) sourceC1096) = raw18342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw18342; decide +kernel
    rw [ha]
    exact (canonical18342 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1096 + difference 5 2) (sourceB1096 + difference 2 5) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1096 + difference 5 2) (sourceB1096 + difference 2 5) sourceC1096) = raw18343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw18343; decide +kernel
    rw [ha]
    exact (canonical18343 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1096 + difference 5 3) (sourceB1096 + difference 3 5) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1096 + difference 5 3) (sourceB1096 + difference 3 5) sourceC1096) = raw18344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw18344; decide +kernel
    rw [ha]
    exact (canonical18344 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1096 + difference 5 4) (sourceB1096 + difference 4 5) sourceC1096) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1096 + difference 5 4) (sourceB1096 + difference 4 5) sourceC1096) = raw2935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1096 sourceB1096 sourceC1096 difference raw2935; decide +kernel
    rw [ha]
    exact (canonical2935 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1096 sourceB1096 sourceC1096
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1096, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1097 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1097 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC1097 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1097 : Integer.Sparse Master := [(Sum.inr 5166, 1), (Sum.inr 5168, 1), (Sum.inr 5170, 2), (Sum.inr 5306, 1), (Sum.inr 5383, 1), (Sum.inr 5384, 2), (Sum.inr 5387, 1), (Sum.inr 5403, 2), (Sum.inr 5412, 2), (Sum.inr 5415, 1), (Sum.inr 5437, 1), (Sum.inr 5439, 4), (Sum.inr 5441, 2), (Sum.inr 5443, 2), (Sum.inr 5448, 1), (Sum.inr 5453, 1), (Sum.inr 5455, 2), (Sum.inr 5488, 1), (Sum.inr 5491, 2)]

theorem sourceEq1097 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1097 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1097 + difference 0 1) (sourceB1097 + difference 1 0) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1097 + difference 0 1) (sourceB1097 + difference 1 0) sourceC1097) = raw18345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18345; decide +kernel
    rw [ha]
    exact (canonical18345 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1097 + difference 0 2) (sourceB1097 + difference 2 0) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5488) := by
    have ha : (tripleCharges (sourceA1097 + difference 0 2) (sourceB1097 + difference 2 0) sourceC1097) = raw18346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18346; decide +kernel
    rw [ha]
    exact (canonical18346 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1097 + difference 0 3) (sourceB1097 + difference 3 0) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1097 + difference 0 3) (sourceB1097 + difference 3 0) sourceC1097) = raw18298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18298; decide +kernel
    rw [ha]
    exact (canonical18298 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1097 + difference 0 4) (sourceB1097 + difference 4 0) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1097 + difference 0 4) (sourceB1097 + difference 4 0) sourceC1097) = raw18347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18347; decide +kernel
    rw [ha]
    exact (canonical18347 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1097 + difference 0 5) (sourceB1097 + difference 5 0) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1097 + difference 0 5) (sourceB1097 + difference 5 0) sourceC1097) = raw18348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18348; decide +kernel
    rw [ha]
    exact (canonical18348 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1097 + difference 1 0) (sourceB1097 + difference 0 1) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA1097 + difference 1 0) (sourceB1097 + difference 0 1) sourceC1097) = raw10231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw10231; decide +kernel
    rw [ha]
    exact (canonical10231 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1097 + difference 1 2) (sourceB1097 + difference 2 1) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1097 + difference 1 2) (sourceB1097 + difference 2 1) sourceC1097) = raw12081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw12081; decide +kernel
    rw [ha]
    exact (canonical12081 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1097 + difference 1 3) (sourceB1097 + difference 3 1) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA1097 + difference 1 3) (sourceB1097 + difference 3 1) sourceC1097) = raw10219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw10219; decide +kernel
    rw [ha]
    exact (canonical10219 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1097 + difference 1 4) (sourceB1097 + difference 4 1) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA1097 + difference 1 4) (sourceB1097 + difference 4 1) sourceC1097) = raw12082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw12082; decide +kernel
    rw [ha]
    exact (canonical12082 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1097 + difference 1 5) (sourceB1097 + difference 5 1) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA1097 + difference 1 5) (sourceB1097 + difference 5 1) sourceC1097) = raw12083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw12083; decide +kernel
    rw [ha]
    exact (canonical12083 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1097 + difference 2 0) (sourceB1097 + difference 0 2) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA1097 + difference 2 0) (sourceB1097 + difference 0 2) sourceC1097) = raw12089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw12089; decide +kernel
    rw [ha]
    exact (canonical12089 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1097 + difference 2 1) (sourceB1097 + difference 1 2) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA1097 + difference 2 1) (sourceB1097 + difference 1 2) sourceC1097) = raw18349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18349; decide +kernel
    rw [ha]
    exact (canonical18349 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1097 + difference 2 3) (sourceB1097 + difference 3 2) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1097 + difference 2 3) (sourceB1097 + difference 3 2) sourceC1097) = raw18302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18302; decide +kernel
    rw [ha]
    exact (canonical18302 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1097 + difference 2 4) (sourceB1097 + difference 4 2) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1097 + difference 2 4) (sourceB1097 + difference 4 2) sourceC1097) = raw18350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18350; decide +kernel
    rw [ha]
    exact (canonical18350 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1097 + difference 2 5) (sourceB1097 + difference 5 2) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA1097 + difference 2 5) (sourceB1097 + difference 5 2) sourceC1097) = raw18351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18351; decide +kernel
    rw [ha]
    exact (canonical18351 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1097 + difference 3 0) (sourceB1097 + difference 0 3) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA1097 + difference 3 0) (sourceB1097 + difference 0 3) sourceC1097) = raw12093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw12093; decide +kernel
    rw [ha]
    exact (canonical12093 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1097 + difference 3 1) (sourceB1097 + difference 1 3) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1097 + difference 3 1) (sourceB1097 + difference 1 3) sourceC1097) = raw18352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18352; decide +kernel
    rw [ha]
    exact (canonical18352 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1097 + difference 3 2) (sourceB1097 + difference 2 3) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1097 + difference 3 2) (sourceB1097 + difference 2 3) sourceC1097) = raw18353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18353; decide +kernel
    rw [ha]
    exact (canonical18353 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1097 + difference 3 4) (sourceB1097 + difference 4 3) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1097 + difference 3 4) (sourceB1097 + difference 4 3) sourceC1097) = raw18354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18354; decide +kernel
    rw [ha]
    exact (canonical18354 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1097 + difference 3 5) (sourceB1097 + difference 5 3) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1097 + difference 3 5) (sourceB1097 + difference 5 3) sourceC1097) = raw18355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18355; decide +kernel
    rw [ha]
    exact (canonical18355 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1097 + difference 4 0) (sourceB1097 + difference 0 4) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA1097 + difference 4 0) (sourceB1097 + difference 0 4) sourceC1097) = raw12098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw12098; decide +kernel
    rw [ha]
    exact (canonical12098 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1097 + difference 4 1) (sourceB1097 + difference 1 4) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1097 + difference 4 1) (sourceB1097 + difference 1 4) sourceC1097) = raw18356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18356; decide +kernel
    rw [ha]
    exact (canonical18356 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1097 + difference 4 2) (sourceB1097 + difference 2 4) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1097 + difference 4 2) (sourceB1097 + difference 2 4) sourceC1097) = raw18357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18357; decide +kernel
    rw [ha]
    exact (canonical18357 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1097 + difference 4 3) (sourceB1097 + difference 3 4) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1097 + difference 4 3) (sourceB1097 + difference 3 4) sourceC1097) = raw18309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18309; decide +kernel
    rw [ha]
    exact (canonical18309 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1097 + difference 4 5) (sourceB1097 + difference 5 4) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1097 + difference 4 5) (sourceB1097 + difference 5 4) sourceC1097) = raw18358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18358; decide +kernel
    rw [ha]
    exact (canonical18358 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1097 + difference 5 0) (sourceB1097 + difference 0 5) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1097 + difference 5 0) (sourceB1097 + difference 0 5) sourceC1097) = raw10229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw10229; decide +kernel
    rw [ha]
    exact (canonical10229 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1097 + difference 5 1) (sourceB1097 + difference 1 5) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1097 + difference 5 1) (sourceB1097 + difference 1 5) sourceC1097) = raw18303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18303; decide +kernel
    rw [ha]
    exact (canonical18303 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1097 + difference 5 2) (sourceB1097 + difference 2 5) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA1097 + difference 5 2) (sourceB1097 + difference 2 5) sourceC1097) = raw18304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18304; decide +kernel
    rw [ha]
    exact (canonical18304 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1097 + difference 5 3) (sourceB1097 + difference 3 5) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1097 + difference 5 3) (sourceB1097 + difference 3 5) sourceC1097) = raw10216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw10216; decide +kernel
    rw [ha]
    exact (canonical10216 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1097 + difference 5 4) (sourceB1097 + difference 4 5) sourceC1097) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1097 + difference 5 4) (sourceB1097 + difference 4 5) sourceC1097) = raw18305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1097 sourceB1097 sourceC1097 difference raw18305; decide +kernel
    rw [ha]
    exact (canonical18305 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1097 sourceB1097 sourceC1097
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1097, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1098 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1098 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC1098 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceForm1098 : Integer.Sparse Master := [(Sum.inr 5148, 1), (Sum.inr 5149, 2), (Sum.inr 5167, 1), (Sum.inr 5292, 1), (Sum.inr 5378, 2), (Sum.inr 5380, 1), (Sum.inr 5386, 1), (Sum.inr 5397, 2), (Sum.inr 5406, 2), (Sum.inr 5422, 1), (Sum.inr 5431, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5435, 2), (Sum.inr 5440, 2), (Sum.inr 5450, 1), (Sum.inr 5452, 1), (Sum.inr 5454, 2), (Sum.inr 5481, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2)]

theorem sourceEq1098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1098 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1098 + difference 0 1) (sourceB1098 + difference 1 0) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1098 + difference 0 1) (sourceB1098 + difference 1 0) sourceC1098) = raw18359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18359; decide +kernel
    rw [ha]
    exact (canonical18359 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1098 + difference 0 2) (sourceB1098 + difference 2 0) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1098 + difference 0 2) (sourceB1098 + difference 2 0) sourceC1098) = raw18360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18360; decide +kernel
    rw [ha]
    exact (canonical18360 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1098 + difference 0 3) (sourceB1098 + difference 3 0) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1098 + difference 0 3) (sourceB1098 + difference 3 0) sourceC1098) = raw18361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18361; decide +kernel
    rw [ha]
    exact (canonical18361 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1098 + difference 0 4) (sourceB1098 + difference 4 0) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1098 + difference 0 4) (sourceB1098 + difference 4 0) sourceC1098) = raw18362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18362; decide +kernel
    rw [ha]
    exact (canonical18362 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1098 + difference 0 5) (sourceB1098 + difference 5 0) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1098 + difference 0 5) (sourceB1098 + difference 5 0) sourceC1098) = raw18363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18363; decide +kernel
    rw [ha]
    exact (canonical18363 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1098 + difference 1 0) (sourceB1098 + difference 0 1) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1098 + difference 1 0) (sourceB1098 + difference 0 1) sourceC1098) = raw18364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18364; decide +kernel
    rw [ha]
    exact (canonical18364 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1098 + difference 1 2) (sourceB1098 + difference 2 1) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1098 + difference 1 2) (sourceB1098 + difference 2 1) sourceC1098) = raw12532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12532; decide +kernel
    rw [ha]
    exact (canonical12532 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1098 + difference 1 3) (sourceB1098 + difference 3 1) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA1098 + difference 1 3) (sourceB1098 + difference 3 1) sourceC1098) = raw12533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12533; decide +kernel
    rw [ha]
    exact (canonical12533 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1098 + difference 1 4) (sourceB1098 + difference 4 1) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA1098 + difference 1 4) (sourceB1098 + difference 4 1) sourceC1098) = raw12534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12534; decide +kernel
    rw [ha]
    exact (canonical12534 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1098 + difference 1 5) (sourceB1098 + difference 5 1) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1098 + difference 1 5) (sourceB1098 + difference 5 1) sourceC1098) = raw12535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12535; decide +kernel
    rw [ha]
    exact (canonical12535 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1098 + difference 2 0) (sourceB1098 + difference 0 2) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA1098 + difference 2 0) (sourceB1098 + difference 0 2) sourceC1098) = raw12542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12542; decide +kernel
    rw [ha]
    exact (canonical12542 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1098 + difference 2 1) (sourceB1098 + difference 1 2) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA1098 + difference 2 1) (sourceB1098 + difference 1 2) sourceC1098) = raw18365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18365; decide +kernel
    rw [ha]
    exact (canonical18365 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1098 + difference 2 3) (sourceB1098 + difference 3 2) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1098 + difference 2 3) (sourceB1098 + difference 3 2) sourceC1098) = raw18366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18366; decide +kernel
    rw [ha]
    exact (canonical18366 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1098 + difference 2 4) (sourceB1098 + difference 4 2) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1098 + difference 2 4) (sourceB1098 + difference 4 2) sourceC1098) = raw18367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18367; decide +kernel
    rw [ha]
    exact (canonical18367 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1098 + difference 2 5) (sourceB1098 + difference 5 2) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1098 + difference 2 5) (sourceB1098 + difference 5 2) sourceC1098) = raw18368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18368; decide +kernel
    rw [ha]
    exact (canonical18368 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1098 + difference 3 0) (sourceB1098 + difference 0 3) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1098 + difference 3 0) (sourceB1098 + difference 0 3) sourceC1098) = raw12547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12547; decide +kernel
    rw [ha]
    exact (canonical12547 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1098 + difference 3 1) (sourceB1098 + difference 1 3) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1098 + difference 3 1) (sourceB1098 + difference 1 3) sourceC1098) = raw18369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18369; decide +kernel
    rw [ha]
    exact (canonical18369 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1098 + difference 3 2) (sourceB1098 + difference 2 3) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1098 + difference 3 2) (sourceB1098 + difference 2 3) sourceC1098) = raw18370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18370; decide +kernel
    rw [ha]
    exact (canonical18370 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1098 + difference 3 4) (sourceB1098 + difference 4 3) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1098 + difference 3 4) (sourceB1098 + difference 4 3) sourceC1098) = raw18371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18371; decide +kernel
    rw [ha]
    exact (canonical18371 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1098 + difference 3 5) (sourceB1098 + difference 5 3) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1098 + difference 3 5) (sourceB1098 + difference 5 3) sourceC1098) = raw18372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18372; decide +kernel
    rw [ha]
    exact (canonical18372 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1098 + difference 4 0) (sourceB1098 + difference 0 4) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1098 + difference 4 0) (sourceB1098 + difference 0 4) sourceC1098) = raw12552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12552; decide +kernel
    rw [ha]
    exact (canonical12552 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1098 + difference 4 1) (sourceB1098 + difference 1 4) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1098 + difference 4 1) (sourceB1098 + difference 1 4) sourceC1098) = raw18373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18373; decide +kernel
    rw [ha]
    exact (canonical18373 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1098 + difference 4 2) (sourceB1098 + difference 2 4) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1098 + difference 4 2) (sourceB1098 + difference 2 4) sourceC1098) = raw18374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18374; decide +kernel
    rw [ha]
    exact (canonical18374 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1098 + difference 4 3) (sourceB1098 + difference 3 4) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1098 + difference 4 3) (sourceB1098 + difference 3 4) sourceC1098) = raw18375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18375; decide +kernel
    rw [ha]
    exact (canonical18375 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1098 + difference 4 5) (sourceB1098 + difference 5 4) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1098 + difference 4 5) (sourceB1098 + difference 5 4) sourceC1098) = raw18376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18376; decide +kernel
    rw [ha]
    exact (canonical18376 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1098 + difference 5 0) (sourceB1098 + difference 0 5) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA1098 + difference 5 0) (sourceB1098 + difference 0 5) sourceC1098) = raw12557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12557; decide +kernel
    rw [ha]
    exact (canonical12557 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1098 + difference 5 1) (sourceB1098 + difference 1 5) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1098 + difference 5 1) (sourceB1098 + difference 1 5) sourceC1098) = raw18377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18377; decide +kernel
    rw [ha]
    exact (canonical18377 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1098 + difference 5 2) (sourceB1098 + difference 2 5) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1098 + difference 5 2) (sourceB1098 + difference 2 5) sourceC1098) = raw18378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18378; decide +kernel
    rw [ha]
    exact (canonical18378 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1098 + difference 5 3) (sourceB1098 + difference 3 5) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1098 + difference 5 3) (sourceB1098 + difference 3 5) sourceC1098) = raw18379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18379; decide +kernel
    rw [ha]
    exact (canonical18379 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1098 + difference 5 4) (sourceB1098 + difference 4 5) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1098 + difference 5 4) (sourceB1098 + difference 4 5) sourceC1098) = raw18380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18380; decide +kernel
    rw [ha]
    exact (canonical18380 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1098 sourceB1098 sourceC1098
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1098, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1099 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1099 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1099 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceForm1099 : Integer.Sparse Master := [(Sum.inr 4801, 1), (Sum.inr 4802, 2), (Sum.inr 4831, 1), (Sum.inr 4887, 1), (Sum.inr 5351, 1), (Sum.inr 5352, 2), (Sum.inr 5365, 1), (Sum.inr 5415, 1), (Sum.inr 5416, 2), (Sum.inr 5423, 2), (Sum.inr 5424, 4), (Sum.inr 5433, 3), (Sum.inr 5434, 2), (Sum.inr 5439, 1), (Sum.inr 5452, 1), (Sum.inr 5482, 1), (Sum.inr 5497, 1), (Sum.inr 5499, 1), (Sum.inr 5500, 2)]

theorem sourceEq1099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1099 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1099 + difference 0 1) (sourceB1099 + difference 1 0) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1099 + difference 0 1) (sourceB1099 + difference 1 0) sourceC1099) = raw18381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18381; decide +kernel
    rw [ha]
    exact (canonical18381 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1099 + difference 0 2) (sourceB1099 + difference 2 0) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5497) := by
    have ha : (tripleCharges (sourceA1099 + difference 0 2) (sourceB1099 + difference 2 0) sourceC1099) = raw18382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18382; decide +kernel
    rw [ha]
    exact (canonical18382 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1099 + difference 0 3) (sourceB1099 + difference 3 0) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA1099 + difference 0 3) (sourceB1099 + difference 3 0) sourceC1099) = raw18268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18268; decide +kernel
    rw [ha]
    exact (canonical18268 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1099 + difference 0 4) (sourceB1099 + difference 4 0) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA1099 + difference 0 4) (sourceB1099 + difference 4 0) sourceC1099) = raw18383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18383; decide +kernel
    rw [ha]
    exact (canonical18383 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1099 + difference 0 5) (sourceB1099 + difference 5 0) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA1099 + difference 0 5) (sourceB1099 + difference 5 0) sourceC1099) = raw18384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18384; decide +kernel
    rw [ha]
    exact (canonical18384 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1099 + difference 1 0) (sourceB1099 + difference 0 1) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA1099 + difference 1 0) (sourceB1099 + difference 0 1) sourceC1099) = raw18385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18385; decide +kernel
    rw [ha]
    exact (canonical18385 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1099 + difference 1 2) (sourceB1099 + difference 2 1) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1099 + difference 1 2) (sourceB1099 + difference 2 1) sourceC1099) = raw18386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18386; decide +kernel
    rw [ha]
    exact (canonical18386 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1099 + difference 1 3) (sourceB1099 + difference 3 1) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1099 + difference 1 3) (sourceB1099 + difference 3 1) sourceC1099) = raw18273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18273; decide +kernel
    rw [ha]
    exact (canonical18273 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1099 + difference 1 4) (sourceB1099 + difference 4 1) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1099 + difference 1 4) (sourceB1099 + difference 4 1) sourceC1099) = raw18387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18387; decide +kernel
    rw [ha]
    exact (canonical18387 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1099 + difference 1 5) (sourceB1099 + difference 5 1) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1099 + difference 1 5) (sourceB1099 + difference 5 1) sourceC1099) = raw18388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18388; decide +kernel
    rw [ha]
    exact (canonical18388 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1099 + difference 2 0) (sourceB1099 + difference 0 2) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA1099 + difference 2 0) (sourceB1099 + difference 0 2) sourceC1099) = raw18389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18389; decide +kernel
    rw [ha]
    exact (canonical18389 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1099 + difference 2 1) (sourceB1099 + difference 1 2) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1099 + difference 2 1) (sourceB1099 + difference 1 2) sourceC1099) = raw18390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18390; decide +kernel
    rw [ha]
    exact (canonical18390 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1099 + difference 2 3) (sourceB1099 + difference 3 2) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1099 + difference 2 3) (sourceB1099 + difference 3 2) sourceC1099) = raw18278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18278; decide +kernel
    rw [ha]
    exact (canonical18278 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1099 + difference 2 4) (sourceB1099 + difference 4 2) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1099 + difference 2 4) (sourceB1099 + difference 4 2) sourceC1099) = raw18391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18391; decide +kernel
    rw [ha]
    exact (canonical18391 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1099 + difference 2 5) (sourceB1099 + difference 5 2) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1099 + difference 2 5) (sourceB1099 + difference 5 2) sourceC1099) = raw18392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18392; decide +kernel
    rw [ha]
    exact (canonical18392 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1099 + difference 3 0) (sourceB1099 + difference 0 3) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA1099 + difference 3 0) (sourceB1099 + difference 0 3) sourceC1099) = raw18393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18393; decide +kernel
    rw [ha]
    exact (canonical18393 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1099 + difference 3 1) (sourceB1099 + difference 1 3) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1099 + difference 3 1) (sourceB1099 + difference 1 3) sourceC1099) = raw18394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18394; decide +kernel
    rw [ha]
    exact (canonical18394 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1099 + difference 3 2) (sourceB1099 + difference 2 3) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1099 + difference 3 2) (sourceB1099 + difference 2 3) sourceC1099) = raw18395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18395; decide +kernel
    rw [ha]
    exact (canonical18395 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1099 + difference 3 4) (sourceB1099 + difference 4 3) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1099 + difference 3 4) (sourceB1099 + difference 4 3) sourceC1099) = raw18396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18396; decide +kernel
    rw [ha]
    exact (canonical18396 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1099 + difference 3 5) (sourceB1099 + difference 5 3) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1099 + difference 3 5) (sourceB1099 + difference 5 3) sourceC1099) = raw18397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18397; decide +kernel
    rw [ha]
    exact (canonical18397 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1099 + difference 4 0) (sourceB1099 + difference 0 4) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA1099 + difference 4 0) (sourceB1099 + difference 0 4) sourceC1099) = raw18398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18398; decide +kernel
    rw [ha]
    exact (canonical18398 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1099 + difference 4 1) (sourceB1099 + difference 1 4) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1099 + difference 4 1) (sourceB1099 + difference 1 4) sourceC1099) = raw18399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18399; decide +kernel
    rw [ha]
    exact (canonical18399 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1099 + difference 4 2) (sourceB1099 + difference 2 4) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1099 + difference 4 2) (sourceB1099 + difference 2 4) sourceC1099) = raw18400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18400; decide +kernel
    rw [ha]
    exact (canonical18400 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1099 + difference 4 3) (sourceB1099 + difference 3 4) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1099 + difference 4 3) (sourceB1099 + difference 3 4) sourceC1099) = raw18288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18288; decide +kernel
    rw [ha]
    exact (canonical18288 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1099 + difference 4 5) (sourceB1099 + difference 5 4) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1099 + difference 4 5) (sourceB1099 + difference 5 4) sourceC1099) = raw18401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18401; decide +kernel
    rw [ha]
    exact (canonical18401 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1099 + difference 5 0) (sourceB1099 + difference 0 5) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA1099 + difference 5 0) (sourceB1099 + difference 0 5) sourceC1099) = raw18279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18279; decide +kernel
    rw [ha]
    exact (canonical18279 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1099 + difference 5 1) (sourceB1099 + difference 1 5) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1099 + difference 5 1) (sourceB1099 + difference 1 5) sourceC1099) = raw18280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18280; decide +kernel
    rw [ha]
    exact (canonical18280 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1099 + difference 5 2) (sourceB1099 + difference 2 5) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA1099 + difference 5 2) (sourceB1099 + difference 2 5) sourceC1099) = raw18281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18281; decide +kernel
    rw [ha]
    exact (canonical18281 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1099 + difference 5 3) (sourceB1099 + difference 3 5) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1099 + difference 5 3) (sourceB1099 + difference 3 5) sourceC1099) = raw18402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18402; decide +kernel
    rw [ha]
    exact (canonical18402 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1099 + difference 5 4) (sourceB1099 + difference 4 5) sourceC1099) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1099 + difference 5 4) (sourceB1099 + difference 4 5) sourceC1099) = raw18282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1099 sourceB1099 sourceC1099 difference raw18282; decide +kernel
    rw [ha]
    exact (canonical18282 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1099 sourceB1099 sourceC1099
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1099, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1100 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceB1100 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1100 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceForm1100 : Integer.Sparse Master := [(Sum.inr 5250, 1), (Sum.inr 5251, 1), (Sum.inr 5257, 2), (Sum.inr 5281, 1), (Sum.inr 5405, 1), (Sum.inr 5406, 1), (Sum.inr 5408, 2), (Sum.inr 5425, 2), (Sum.inr 5430, 2), (Sum.inr 5431, 2), (Sum.inr 5433, 2), (Sum.inr 5437, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 2), (Sum.inr 5445, 2), (Sum.inr 5447, 1), (Sum.inr 5450, 1), (Sum.inr 5478, 2), (Sum.inr 5479, 1), (Sum.inr 5482, 1), (Sum.inr 5486, 1)]

theorem sourceEq1100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1100 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1100 + difference 0 1) (sourceB1100 + difference 1 0) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1100 + difference 0 1) (sourceB1100 + difference 1 0) sourceC1100) = raw18403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18403; decide +kernel
    rw [ha]
    exact (canonical18403 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1100 + difference 0 2) (sourceB1100 + difference 2 0) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1100 + difference 0 2) (sourceB1100 + difference 2 0) sourceC1100) = raw18404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18404; decide +kernel
    rw [ha]
    exact (canonical18404 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1100 + difference 0 3) (sourceB1100 + difference 3 0) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1100 + difference 0 3) (sourceB1100 + difference 3 0) sourceC1100) = raw18405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18405; decide +kernel
    rw [ha]
    exact (canonical18405 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1100 + difference 0 4) (sourceB1100 + difference 4 0) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1100 + difference 0 4) (sourceB1100 + difference 4 0) sourceC1100) = raw18406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18406; decide +kernel
    rw [ha]
    exact (canonical18406 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1100 + difference 0 5) (sourceB1100 + difference 5 0) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5479) := by
    have ha : (tripleCharges (sourceA1100 + difference 0 5) (sourceB1100 + difference 5 0) sourceC1100) = raw18407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18407; decide +kernel
    rw [ha]
    exact (canonical18407 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1100 + difference 1 0) (sourceB1100 + difference 0 1) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1100 + difference 1 0) (sourceB1100 + difference 0 1) sourceC1100) = raw18408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18408; decide +kernel
    rw [ha]
    exact (canonical18408 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1100 + difference 1 2) (sourceB1100 + difference 2 1) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1100 + difference 1 2) (sourceB1100 + difference 2 1) sourceC1100) = raw18409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18409; decide +kernel
    rw [ha]
    exact (canonical18409 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1100 + difference 1 3) (sourceB1100 + difference 3 1) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1100 + difference 1 3) (sourceB1100 + difference 3 1) sourceC1100) = raw18410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18410; decide +kernel
    rw [ha]
    exact (canonical18410 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1100 + difference 1 4) (sourceB1100 + difference 4 1) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1100 + difference 1 4) (sourceB1100 + difference 4 1) sourceC1100) = raw18411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18411; decide +kernel
    rw [ha]
    exact (canonical18411 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1100 + difference 1 5) (sourceB1100 + difference 5 1) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1100 + difference 1 5) (sourceB1100 + difference 5 1) sourceC1100) = raw18412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18412; decide +kernel
    rw [ha]
    exact (canonical18412 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1100 + difference 2 0) (sourceB1100 + difference 0 2) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA1100 + difference 2 0) (sourceB1100 + difference 0 2) sourceC1100) = raw18413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18413; decide +kernel
    rw [ha]
    exact (canonical18413 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1100 + difference 2 1) (sourceB1100 + difference 1 2) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1100 + difference 2 1) (sourceB1100 + difference 1 2) sourceC1100) = raw18414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18414; decide +kernel
    rw [ha]
    exact (canonical18414 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1100 + difference 2 3) (sourceB1100 + difference 3 2) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1100 + difference 2 3) (sourceB1100 + difference 3 2) sourceC1100) = raw18415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18415; decide +kernel
    rw [ha]
    exact (canonical18415 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1100 + difference 2 4) (sourceB1100 + difference 4 2) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1100 + difference 2 4) (sourceB1100 + difference 4 2) sourceC1100) = raw18416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18416; decide +kernel
    rw [ha]
    exact (canonical18416 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1100 + difference 2 5) (sourceB1100 + difference 5 2) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA1100 + difference 2 5) (sourceB1100 + difference 5 2) sourceC1100) = raw18417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18417; decide +kernel
    rw [ha]
    exact (canonical18417 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1100 + difference 3 0) (sourceB1100 + difference 0 3) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1100 + difference 3 0) (sourceB1100 + difference 0 3) sourceC1100) = raw18418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18418; decide +kernel
    rw [ha]
    exact (canonical18418 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1100 + difference 3 1) (sourceB1100 + difference 1 3) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1100 + difference 3 1) (sourceB1100 + difference 1 3) sourceC1100) = raw18419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18419; decide +kernel
    rw [ha]
    exact (canonical18419 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1100 + difference 3 2) (sourceB1100 + difference 2 3) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1100 + difference 3 2) (sourceB1100 + difference 2 3) sourceC1100) = raw18420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18420; decide +kernel
    rw [ha]
    exact (canonical18420 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1100 + difference 3 4) (sourceB1100 + difference 4 3) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1100 + difference 3 4) (sourceB1100 + difference 4 3) sourceC1100) = raw18421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18421; decide +kernel
    rw [ha]
    exact (canonical18421 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1100 + difference 3 5) (sourceB1100 + difference 5 3) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1100 + difference 3 5) (sourceB1100 + difference 5 3) sourceC1100) = raw18422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18422; decide +kernel
    rw [ha]
    exact (canonical18422 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1100 + difference 4 0) (sourceB1100 + difference 0 4) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1100 + difference 4 0) (sourceB1100 + difference 0 4) sourceC1100) = raw18423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18423; decide +kernel
    rw [ha]
    exact (canonical18423 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1100 + difference 4 1) (sourceB1100 + difference 1 4) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1100 + difference 4 1) (sourceB1100 + difference 1 4) sourceC1100) = raw18424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18424; decide +kernel
    rw [ha]
    exact (canonical18424 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1100 + difference 4 2) (sourceB1100 + difference 2 4) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1100 + difference 4 2) (sourceB1100 + difference 2 4) sourceC1100) = raw18425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18425; decide +kernel
    rw [ha]
    exact (canonical18425 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1100 + difference 4 3) (sourceB1100 + difference 3 4) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1100 + difference 4 3) (sourceB1100 + difference 3 4) sourceC1100) = raw18426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18426; decide +kernel
    rw [ha]
    exact (canonical18426 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1100 + difference 4 5) (sourceB1100 + difference 5 4) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1100 + difference 4 5) (sourceB1100 + difference 5 4) sourceC1100) = raw18427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18427; decide +kernel
    rw [ha]
    exact (canonical18427 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1100 + difference 5 0) (sourceB1100 + difference 0 5) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA1100 + difference 5 0) (sourceB1100 + difference 0 5) sourceC1100) = raw18428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18428; decide +kernel
    rw [ha]
    exact (canonical18428 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1100 + difference 5 1) (sourceB1100 + difference 1 5) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1100 + difference 5 1) (sourceB1100 + difference 1 5) sourceC1100) = raw18429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18429; decide +kernel
    rw [ha]
    exact (canonical18429 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1100 + difference 5 2) (sourceB1100 + difference 2 5) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1100 + difference 5 2) (sourceB1100 + difference 2 5) sourceC1100) = raw18430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18430; decide +kernel
    rw [ha]
    exact (canonical18430 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1100 + difference 5 3) (sourceB1100 + difference 3 5) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1100 + difference 5 3) (sourceB1100 + difference 3 5) sourceC1100) = raw18431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18431; decide +kernel
    rw [ha]
    exact (canonical18431 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1100 + difference 5 4) (sourceB1100 + difference 4 5) sourceC1100) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1100 + difference 5 4) (sourceB1100 + difference 4 5) sourceC1100) = raw18432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1100 sourceB1100 sourceC1100 difference raw18432; decide +kernel
    rw [ha]
    exact (canonical18432 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1100 sourceB1100 sourceC1100
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1100, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1101 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1101 : Charge := ![0, 1, 2, -1, -1, -1]
def sourceC1101 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceForm1101 : Integer.Sparse Master := [(Sum.inr 5155, 6), (Sum.inr 5166, 2), (Sum.inr 5301, 2), (Sum.inr 5374, 3), (Sum.inr 5383, 2), (Sum.inr 5412, 6), (Sum.inr 5439, 6), (Sum.inr 5453, 3)]

theorem sourceEq1101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1101 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1101 + difference 0 1) (sourceB1101 + difference 1 0) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA1101 + difference 0 1) (sourceB1101 + difference 1 0) sourceC1101) = raw18433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18433; decide +kernel
    rw [ha]
    exact (canonical18433 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1101 + difference 0 2) (sourceB1101 + difference 2 0) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA1101 + difference 0 2) (sourceB1101 + difference 2 0) sourceC1101) = raw18434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18434; decide +kernel
    rw [ha]
    exact (canonical18434 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1101 + difference 0 3) (sourceB1101 + difference 3 0) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 0 3) (sourceB1101 + difference 3 0) sourceC1101) = raw18435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18435; decide +kernel
    rw [ha]
    exact (canonical18435 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1101 + difference 0 4) (sourceB1101 + difference 4 0) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 0 4) (sourceB1101 + difference 4 0) sourceC1101) = raw18436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18436; decide +kernel
    rw [ha]
    exact (canonical18436 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1101 + difference 0 5) (sourceB1101 + difference 5 0) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 0 5) (sourceB1101 + difference 5 0) sourceC1101) = raw18437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18437; decide +kernel
    rw [ha]
    exact (canonical18437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1101 + difference 1 0) (sourceB1101 + difference 0 1) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA1101 + difference 1 0) (sourceB1101 + difference 0 1) sourceC1101) = raw18438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18438; decide +kernel
    rw [ha]
    exact (canonical18438 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1101 + difference 1 2) (sourceB1101 + difference 2 1) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA1101 + difference 1 2) (sourceB1101 + difference 2 1) sourceC1101) = raw12939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12939; decide +kernel
    rw [ha]
    exact (canonical12939 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1101 + difference 1 3) (sourceB1101 + difference 3 1) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA1101 + difference 1 3) (sourceB1101 + difference 3 1) sourceC1101) = raw12940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12940; decide +kernel
    rw [ha]
    exact (canonical12940 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1101 + difference 1 4) (sourceB1101 + difference 4 1) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA1101 + difference 1 4) (sourceB1101 + difference 4 1) sourceC1101) = raw12941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12941; decide +kernel
    rw [ha]
    exact (canonical12941 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1101 + difference 1 5) (sourceB1101 + difference 5 1) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA1101 + difference 1 5) (sourceB1101 + difference 5 1) sourceC1101) = raw12942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12942; decide +kernel
    rw [ha]
    exact (canonical12942 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1101 + difference 2 0) (sourceB1101 + difference 0 2) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA1101 + difference 2 0) (sourceB1101 + difference 0 2) sourceC1101) = raw12949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12949; decide +kernel
    rw [ha]
    exact (canonical12949 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1101 + difference 2 1) (sourceB1101 + difference 1 2) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA1101 + difference 2 1) (sourceB1101 + difference 1 2) sourceC1101) = raw18439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18439; decide +kernel
    rw [ha]
    exact (canonical18439 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1101 + difference 2 3) (sourceB1101 + difference 3 2) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 2 3) (sourceB1101 + difference 3 2) sourceC1101) = raw18440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18440; decide +kernel
    rw [ha]
    exact (canonical18440 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1101 + difference 2 4) (sourceB1101 + difference 4 2) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 2 4) (sourceB1101 + difference 4 2) sourceC1101) = raw18441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18441; decide +kernel
    rw [ha]
    exact (canonical18441 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1101 + difference 2 5) (sourceB1101 + difference 5 2) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 2 5) (sourceB1101 + difference 5 2) sourceC1101) = raw18442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18442; decide +kernel
    rw [ha]
    exact (canonical18442 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1101 + difference 3 0) (sourceB1101 + difference 0 3) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 3 0) (sourceB1101 + difference 0 3) sourceC1101) = raw12954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12954; decide +kernel
    rw [ha]
    exact (canonical12954 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1101 + difference 3 1) (sourceB1101 + difference 1 3) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA1101 + difference 3 1) (sourceB1101 + difference 1 3) sourceC1101) = raw18443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18443; decide +kernel
    rw [ha]
    exact (canonical18443 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1101 + difference 3 2) (sourceB1101 + difference 2 3) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 3 2) (sourceB1101 + difference 2 3) sourceC1101) = raw18444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18444; decide +kernel
    rw [ha]
    exact (canonical18444 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1101 + difference 3 4) (sourceB1101 + difference 4 3) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 3 4) (sourceB1101 + difference 4 3) sourceC1101) = raw18445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18445; decide +kernel
    rw [ha]
    exact (canonical18445 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1101 + difference 3 5) (sourceB1101 + difference 5 3) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 3 5) (sourceB1101 + difference 5 3) sourceC1101) = raw18446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18446; decide +kernel
    rw [ha]
    exact (canonical18446 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1101 + difference 4 0) (sourceB1101 + difference 0 4) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 4 0) (sourceB1101 + difference 0 4) sourceC1101) = raw12959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12959; decide +kernel
    rw [ha]
    exact (canonical12959 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1101 + difference 4 1) (sourceB1101 + difference 1 4) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA1101 + difference 4 1) (sourceB1101 + difference 1 4) sourceC1101) = raw18447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18447; decide +kernel
    rw [ha]
    exact (canonical18447 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1101 + difference 4 2) (sourceB1101 + difference 2 4) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 4 2) (sourceB1101 + difference 2 4) sourceC1101) = raw18448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18448; decide +kernel
    rw [ha]
    exact (canonical18448 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1101 + difference 4 3) (sourceB1101 + difference 3 4) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 4 3) (sourceB1101 + difference 3 4) sourceC1101) = raw18449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18449; decide +kernel
    rw [ha]
    exact (canonical18449 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1101 + difference 4 5) (sourceB1101 + difference 5 4) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 4 5) (sourceB1101 + difference 5 4) sourceC1101) = raw18450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18450; decide +kernel
    rw [ha]
    exact (canonical18450 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1101 + difference 5 0) (sourceB1101 + difference 0 5) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 5 0) (sourceB1101 + difference 0 5) sourceC1101) = raw12964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12964; decide +kernel
    rw [ha]
    exact (canonical12964 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1101 + difference 5 1) (sourceB1101 + difference 1 5) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA1101 + difference 5 1) (sourceB1101 + difference 1 5) sourceC1101) = raw18451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18451; decide +kernel
    rw [ha]
    exact (canonical18451 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1101 + difference 5 2) (sourceB1101 + difference 2 5) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 5 2) (sourceB1101 + difference 2 5) sourceC1101) = raw18452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18452; decide +kernel
    rw [ha]
    exact (canonical18452 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1101 + difference 5 3) (sourceB1101 + difference 3 5) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 5 3) (sourceB1101 + difference 3 5) sourceC1101) = raw18453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18453; decide +kernel
    rw [ha]
    exact (canonical18453 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1101 + difference 5 4) (sourceB1101 + difference 4 5) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 5 4) (sourceB1101 + difference 4 5) sourceC1101) = raw18454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18454; decide +kernel
    rw [ha]
    exact (canonical18454 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1101 sourceB1101 sourceC1101
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1101, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1102 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1102 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC1102 : Charge := ![0, 1, 2, -1, -1, -1]
def sourceForm1102 : Integer.Sparse Master := [(Sum.inr 4815, 3), (Sum.inr 4830, 1), (Sum.inr 4885, 1), (Sum.inr 5251, 3), (Sum.inr 5277, 1), (Sum.inr 5359, 3), (Sum.inr 5406, 3), (Sum.inr 5422, 3), (Sum.inr 5425, 6), (Sum.inr 5433, 3), (Sum.inr 5447, 2), (Sum.inr 5479, 1)]

theorem sourceEq1102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1102 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1102 + difference 0 1) (sourceB1102 + difference 1 0) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1102 + difference 0 1) (sourceB1102 + difference 1 0) sourceC1102) = raw18455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18455; decide +kernel
    rw [ha]
    exact (canonical18455 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1102 + difference 0 2) (sourceB1102 + difference 2 0) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5479) := by
    have ha : (tripleCharges (sourceA1102 + difference 0 2) (sourceB1102 + difference 2 0) sourceC1102) = raw18456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18456; decide +kernel
    rw [ha]
    exact (canonical18456 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1102 + difference 0 3) (sourceB1102 + difference 3 0) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1102 + difference 0 3) (sourceB1102 + difference 3 0) sourceC1102) = raw18457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18457; decide +kernel
    rw [ha]
    exact (canonical18457 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1102 + difference 0 4) (sourceB1102 + difference 4 0) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1102 + difference 0 4) (sourceB1102 + difference 4 0) sourceC1102) = raw18458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18458; decide +kernel
    rw [ha]
    exact (canonical18458 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1102 + difference 0 5) (sourceB1102 + difference 5 0) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1102 + difference 0 5) (sourceB1102 + difference 5 0) sourceC1102) = raw18459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18459; decide +kernel
    rw [ha]
    exact (canonical18459 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1102 + difference 1 0) (sourceB1102 + difference 0 1) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA1102 + difference 1 0) (sourceB1102 + difference 0 1) sourceC1102) = raw18460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18460; decide +kernel
    rw [ha]
    exact (canonical18460 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1102 + difference 1 2) (sourceB1102 + difference 2 1) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1102 + difference 1 2) (sourceB1102 + difference 2 1) sourceC1102) = raw18461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18461; decide +kernel
    rw [ha]
    exact (canonical18461 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1102 + difference 1 3) (sourceB1102 + difference 3 1) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1102 + difference 1 3) (sourceB1102 + difference 3 1) sourceC1102) = raw18462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18462; decide +kernel
    rw [ha]
    exact (canonical18462 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1102 + difference 1 4) (sourceB1102 + difference 4 1) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1102 + difference 1 4) (sourceB1102 + difference 4 1) sourceC1102) = raw18463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18463; decide +kernel
    rw [ha]
    exact (canonical18463 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1102 + difference 1 5) (sourceB1102 + difference 5 1) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1102 + difference 1 5) (sourceB1102 + difference 5 1) sourceC1102) = raw18464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18464; decide +kernel
    rw [ha]
    exact (canonical18464 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1102 + difference 2 0) (sourceB1102 + difference 0 2) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4830) := by
    have ha : (tripleCharges (sourceA1102 + difference 2 0) (sourceB1102 + difference 0 2) sourceC1102) = raw18465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18465; decide +kernel
    rw [ha]
    exact (canonical18465 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1102 + difference 2 1) (sourceB1102 + difference 1 2) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5277) := by
    have ha : (tripleCharges (sourceA1102 + difference 2 1) (sourceB1102 + difference 1 2) sourceC1102) = raw18466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18466; decide +kernel
    rw [ha]
    exact (canonical18466 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1102 + difference 2 3) (sourceB1102 + difference 3 2) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA1102 + difference 2 3) (sourceB1102 + difference 3 2) sourceC1102) = raw18467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18467; decide +kernel
    rw [ha]
    exact (canonical18467 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1102 + difference 2 4) (sourceB1102 + difference 4 2) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA1102 + difference 2 4) (sourceB1102 + difference 4 2) sourceC1102) = raw18468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18468; decide +kernel
    rw [ha]
    exact (canonical18468 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1102 + difference 2 5) (sourceB1102 + difference 5 2) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA1102 + difference 2 5) (sourceB1102 + difference 5 2) sourceC1102) = raw18469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18469; decide +kernel
    rw [ha]
    exact (canonical18469 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1102 + difference 3 0) (sourceB1102 + difference 0 3) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA1102 + difference 3 0) (sourceB1102 + difference 0 3) sourceC1102) = raw18470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18470; decide +kernel
    rw [ha]
    exact (canonical18470 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1102 + difference 3 1) (sourceB1102 + difference 1 3) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1102 + difference 3 1) (sourceB1102 + difference 1 3) sourceC1102) = raw18471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18471; decide +kernel
    rw [ha]
    exact (canonical18471 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1102 + difference 3 2) (sourceB1102 + difference 2 3) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1102 + difference 3 2) (sourceB1102 + difference 2 3) sourceC1102) = raw18472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18472; decide +kernel
    rw [ha]
    exact (canonical18472 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1102 + difference 3 4) (sourceB1102 + difference 4 3) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 3 4) (sourceB1102 + difference 4 3) sourceC1102) = raw18473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18473; decide +kernel
    rw [ha]
    exact (canonical18473 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1102 + difference 3 5) (sourceB1102 + difference 5 3) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 3 5) (sourceB1102 + difference 5 3) sourceC1102) = raw18474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18474; decide +kernel
    rw [ha]
    exact (canonical18474 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1102 + difference 4 0) (sourceB1102 + difference 0 4) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA1102 + difference 4 0) (sourceB1102 + difference 0 4) sourceC1102) = raw18475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18475; decide +kernel
    rw [ha]
    exact (canonical18475 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1102 + difference 4 1) (sourceB1102 + difference 1 4) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1102 + difference 4 1) (sourceB1102 + difference 1 4) sourceC1102) = raw18476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18476; decide +kernel
    rw [ha]
    exact (canonical18476 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1102 + difference 4 2) (sourceB1102 + difference 2 4) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1102 + difference 4 2) (sourceB1102 + difference 2 4) sourceC1102) = raw18477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18477; decide +kernel
    rw [ha]
    exact (canonical18477 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1102 + difference 4 3) (sourceB1102 + difference 3 4) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 4 3) (sourceB1102 + difference 3 4) sourceC1102) = raw18478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18478; decide +kernel
    rw [ha]
    exact (canonical18478 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1102 + difference 4 5) (sourceB1102 + difference 5 4) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 4 5) (sourceB1102 + difference 5 4) sourceC1102) = raw18479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18479; decide +kernel
    rw [ha]
    exact (canonical18479 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1102 + difference 5 0) (sourceB1102 + difference 0 5) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA1102 + difference 5 0) (sourceB1102 + difference 0 5) sourceC1102) = raw18480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18480; decide +kernel
    rw [ha]
    exact (canonical18480 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1102 + difference 5 1) (sourceB1102 + difference 1 5) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1102 + difference 5 1) (sourceB1102 + difference 1 5) sourceC1102) = raw18481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18481; decide +kernel
    rw [ha]
    exact (canonical18481 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1102 + difference 5 2) (sourceB1102 + difference 2 5) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1102 + difference 5 2) (sourceB1102 + difference 2 5) sourceC1102) = raw18482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18482; decide +kernel
    rw [ha]
    exact (canonical18482 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1102 + difference 5 3) (sourceB1102 + difference 3 5) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 5 3) (sourceB1102 + difference 3 5) sourceC1102) = raw18483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18483; decide +kernel
    rw [ha]
    exact (canonical18483 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1102 + difference 5 4) (sourceB1102 + difference 4 5) sourceC1102) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1102 + difference 5 4) (sourceB1102 + difference 4 5) sourceC1102) = raw18484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1102 sourceB1102 sourceC1102 difference raw18484; decide +kernel
    rw [ha]
    exact (canonical18484 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1102 sourceB1102 sourceC1102
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1102, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1103 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1103 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1103 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceForm1103 : Integer.Sparse Master := [(Sum.inr 4864, 1), (Sum.inr 4865, 1), (Sum.inr 4866, 2), (Sum.inr 4889, 1), (Sum.inr 5386, 1), (Sum.inr 5387, 1), (Sum.inr 5388, 2), (Sum.inr 5400, 1), (Sum.inr 5401, 2), (Sum.inr 5406, 1), (Sum.inr 5431, 2), (Sum.inr 5432, 2), (Sum.inr 5435, 2), (Sum.inr 5438, 2), (Sum.inr 5440, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 2), (Sum.inr 5453, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2), (Sum.inr 5493, 1)]

theorem sourceEq1103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1103 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1103 + difference 0 1) (sourceB1103 + difference 1 0) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1103 + difference 0 1) (sourceB1103 + difference 1 0) sourceC1103) = raw18485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18485; decide +kernel
    rw [ha]
    exact (canonical18485 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1103 + difference 0 2) (sourceB1103 + difference 2 0) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1103 + difference 0 2) (sourceB1103 + difference 2 0) sourceC1103) = raw18486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18486; decide +kernel
    rw [ha]
    exact (canonical18486 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1103 + difference 0 3) (sourceB1103 + difference 3 0) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1103 + difference 0 3) (sourceB1103 + difference 3 0) sourceC1103) = raw18186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18186; decide +kernel
    rw [ha]
    exact (canonical18186 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1103 + difference 0 4) (sourceB1103 + difference 4 0) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1103 + difference 0 4) (sourceB1103 + difference 4 0) sourceC1103) = raw18487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18487; decide +kernel
    rw [ha]
    exact (canonical18487 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1103 + difference 0 5) (sourceB1103 + difference 5 0) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1103 + difference 0 5) (sourceB1103 + difference 5 0) sourceC1103) = raw18488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18488; decide +kernel
    rw [ha]
    exact (canonical18488 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1103 + difference 1 0) (sourceB1103 + difference 0 1) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA1103 + difference 1 0) (sourceB1103 + difference 0 1) sourceC1103) = raw18489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18489; decide +kernel
    rw [ha]
    exact (canonical18489 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1103 + difference 1 2) (sourceB1103 + difference 2 1) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1103 + difference 1 2) (sourceB1103 + difference 2 1) sourceC1103) = raw18490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18490; decide +kernel
    rw [ha]
    exact (canonical18490 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1103 + difference 1 3) (sourceB1103 + difference 3 1) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1103 + difference 1 3) (sourceB1103 + difference 3 1) sourceC1103) = raw18191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18191; decide +kernel
    rw [ha]
    exact (canonical18191 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1103 + difference 1 4) (sourceB1103 + difference 4 1) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1103 + difference 1 4) (sourceB1103 + difference 4 1) sourceC1103) = raw18491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18491; decide +kernel
    rw [ha]
    exact (canonical18491 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1103 + difference 1 5) (sourceB1103 + difference 5 1) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA1103 + difference 1 5) (sourceB1103 + difference 5 1) sourceC1103) = raw18492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18492; decide +kernel
    rw [ha]
    exact (canonical18492 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1103 + difference 2 0) (sourceB1103 + difference 0 2) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA1103 + difference 2 0) (sourceB1103 + difference 0 2) sourceC1103) = raw18493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18493; decide +kernel
    rw [ha]
    exact (canonical18493 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1103 + difference 2 1) (sourceB1103 + difference 1 2) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA1103 + difference 2 1) (sourceB1103 + difference 1 2) sourceC1103) = raw18494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18494; decide +kernel
    rw [ha]
    exact (canonical18494 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1103 + difference 2 3) (sourceB1103 + difference 3 2) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1103 + difference 2 3) (sourceB1103 + difference 3 2) sourceC1103) = raw18196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18196; decide +kernel
    rw [ha]
    exact (canonical18196 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1103 + difference 2 4) (sourceB1103 + difference 4 2) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1103 + difference 2 4) (sourceB1103 + difference 4 2) sourceC1103) = raw18495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18495; decide +kernel
    rw [ha]
    exact (canonical18495 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1103 + difference 2 5) (sourceB1103 + difference 5 2) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1103 + difference 2 5) (sourceB1103 + difference 5 2) sourceC1103) = raw18496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18496; decide +kernel
    rw [ha]
    exact (canonical18496 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1103 + difference 3 0) (sourceB1103 + difference 0 3) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA1103 + difference 3 0) (sourceB1103 + difference 0 3) sourceC1103) = raw18497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18497; decide +kernel
    rw [ha]
    exact (canonical18497 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1103 + difference 3 1) (sourceB1103 + difference 1 3) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA1103 + difference 3 1) (sourceB1103 + difference 1 3) sourceC1103) = raw18498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18498; decide +kernel
    rw [ha]
    exact (canonical18498 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1103 + difference 3 2) (sourceB1103 + difference 2 3) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1103 + difference 3 2) (sourceB1103 + difference 2 3) sourceC1103) = raw18499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18499; decide +kernel
    rw [ha]
    exact (canonical18499 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1103 + difference 3 4) (sourceB1103 + difference 4 3) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1103 + difference 3 4) (sourceB1103 + difference 4 3) sourceC1103) = raw18500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18500; decide +kernel
    rw [ha]
    exact (canonical18500 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1103 + difference 3 5) (sourceB1103 + difference 5 3) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1103 + difference 3 5) (sourceB1103 + difference 5 3) sourceC1103) = raw18501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18501; decide +kernel
    rw [ha]
    exact (canonical18501 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1103 + difference 4 0) (sourceB1103 + difference 0 4) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA1103 + difference 4 0) (sourceB1103 + difference 0 4) sourceC1103) = raw18502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18502; decide +kernel
    rw [ha]
    exact (canonical18502 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1103 + difference 4 1) (sourceB1103 + difference 1 4) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA1103 + difference 4 1) (sourceB1103 + difference 1 4) sourceC1103) = raw18503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18503; decide +kernel
    rw [ha]
    exact (canonical18503 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1103 + difference 4 2) (sourceB1103 + difference 2 4) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1103 + difference 4 2) (sourceB1103 + difference 2 4) sourceC1103) = raw18504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18504; decide +kernel
    rw [ha]
    exact (canonical18504 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1103 + difference 4 3) (sourceB1103 + difference 3 4) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1103 + difference 4 3) (sourceB1103 + difference 3 4) sourceC1103) = raw18206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18206; decide +kernel
    rw [ha]
    exact (canonical18206 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1103 + difference 4 5) (sourceB1103 + difference 5 4) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1103 + difference 4 5) (sourceB1103 + difference 5 4) sourceC1103) = raw18505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18505; decide +kernel
    rw [ha]
    exact (canonical18505 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1103 + difference 5 0) (sourceB1103 + difference 0 5) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA1103 + difference 5 0) (sourceB1103 + difference 0 5) sourceC1103) = raw18197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18197; decide +kernel
    rw [ha]
    exact (canonical18197 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1103 + difference 5 1) (sourceB1103 + difference 1 5) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1103 + difference 5 1) (sourceB1103 + difference 1 5) sourceC1103) = raw18198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18198; decide +kernel
    rw [ha]
    exact (canonical18198 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1103 + difference 5 2) (sourceB1103 + difference 2 5) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1103 + difference 5 2) (sourceB1103 + difference 2 5) sourceC1103) = raw18199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18199; decide +kernel
    rw [ha]
    exact (canonical18199 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1103 + difference 5 3) (sourceB1103 + difference 3 5) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1103 + difference 5 3) (sourceB1103 + difference 3 5) sourceC1103) = raw18506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18506; decide +kernel
    rw [ha]
    exact (canonical18506 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1103 + difference 5 4) (sourceB1103 + difference 4 5) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1103 + difference 5 4) (sourceB1103 + difference 4 5) sourceC1103) = raw18200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18200; decide +kernel
    rw [ha]
    exact (canonical18200 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1103 sourceB1103 sourceC1103
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1103, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1104 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceB1104 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1104 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceForm1104 : Integer.Sparse Master := [(Sum.inr 5265, 1), (Sum.inr 5266, 2), (Sum.inr 5270, 1), (Sum.inr 5281, 1), (Sum.inr 5282, 1), (Sum.inr 5290, 2), (Sum.inr 5301, 1), (Sum.inr 5429, 1), (Sum.inr 5431, 2), (Sum.inr 5433, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 2), (Sum.inr 5445, 2), (Sum.inr 5446, 2), (Sum.inr 5447, 1), (Sum.inr 5448, 2), (Sum.inr 5450, 2), (Sum.inr 5472, 1), (Sum.inr 5473, 2), (Sum.inr 5474, 1), (Sum.inr 5486, 1)]

theorem sourceEq1104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1104 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1104 + difference 0 1) (sourceB1104 + difference 1 0) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1104 + difference 0 1) (sourceB1104 + difference 1 0) sourceC1104) = raw18404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18404; decide +kernel
    rw [ha]
    exact (canonical18404 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1104 + difference 0 2) (sourceB1104 + difference 2 0) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1104 + difference 0 2) (sourceB1104 + difference 2 0) sourceC1104) = raw18507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18507; decide +kernel
    rw [ha]
    exact (canonical18507 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1104 + difference 0 3) (sourceB1104 + difference 3 0) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1104 + difference 0 3) (sourceB1104 + difference 3 0) sourceC1104) = raw18508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18508; decide +kernel
    rw [ha]
    exact (canonical18508 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1104 + difference 0 4) (sourceB1104 + difference 4 0) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1104 + difference 0 4) (sourceB1104 + difference 4 0) sourceC1104) = raw18509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18509; decide +kernel
    rw [ha]
    exact (canonical18509 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1104 + difference 0 5) (sourceB1104 + difference 5 0) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA1104 + difference 0 5) (sourceB1104 + difference 5 0) sourceC1104) = raw18510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18510; decide +kernel
    rw [ha]
    exact (canonical18510 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1104 + difference 1 0) (sourceB1104 + difference 0 1) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA1104 + difference 1 0) (sourceB1104 + difference 0 1) sourceC1104) = raw18511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18511; decide +kernel
    rw [ha]
    exact (canonical18511 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1104 + difference 1 2) (sourceB1104 + difference 2 1) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA1104 + difference 1 2) (sourceB1104 + difference 2 1) sourceC1104) = raw18512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18512; decide +kernel
    rw [ha]
    exact (canonical18512 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1104 + difference 1 3) (sourceB1104 + difference 3 1) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA1104 + difference 1 3) (sourceB1104 + difference 3 1) sourceC1104) = raw18513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18513; decide +kernel
    rw [ha]
    exact (canonical18513 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1104 + difference 1 4) (sourceB1104 + difference 4 1) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA1104 + difference 1 4) (sourceB1104 + difference 4 1) sourceC1104) = raw18514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18514; decide +kernel
    rw [ha]
    exact (canonical18514 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1104 + difference 1 5) (sourceB1104 + difference 5 1) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA1104 + difference 1 5) (sourceB1104 + difference 5 1) sourceC1104) = raw18515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18515; decide +kernel
    rw [ha]
    exact (canonical18515 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1104 + difference 2 0) (sourceB1104 + difference 0 2) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1104 + difference 2 0) (sourceB1104 + difference 0 2) sourceC1104) = raw18408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18408; decide +kernel
    rw [ha]
    exact (canonical18408 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1104 + difference 2 1) (sourceB1104 + difference 1 2) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1104 + difference 2 1) (sourceB1104 + difference 1 2) sourceC1104) = raw18516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18516; decide +kernel
    rw [ha]
    exact (canonical18516 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1104 + difference 2 3) (sourceB1104 + difference 3 2) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1104 + difference 2 3) (sourceB1104 + difference 3 2) sourceC1104) = raw18410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18410; decide +kernel
    rw [ha]
    exact (canonical18410 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1104 + difference 2 4) (sourceB1104 + difference 4 2) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1104 + difference 2 4) (sourceB1104 + difference 4 2) sourceC1104) = raw18411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18411; decide +kernel
    rw [ha]
    exact (canonical18411 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1104 + difference 2 5) (sourceB1104 + difference 5 2) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1104 + difference 2 5) (sourceB1104 + difference 5 2) sourceC1104) = raw18412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18412; decide +kernel
    rw [ha]
    exact (canonical18412 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1104 + difference 3 0) (sourceB1104 + difference 0 3) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1104 + difference 3 0) (sourceB1104 + difference 0 3) sourceC1104) = raw18517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18517; decide +kernel
    rw [ha]
    exact (canonical18517 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1104 + difference 3 1) (sourceB1104 + difference 1 3) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1104 + difference 3 1) (sourceB1104 + difference 1 3) sourceC1104) = raw18420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18420; decide +kernel
    rw [ha]
    exact (canonical18420 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1104 + difference 3 2) (sourceB1104 + difference 2 3) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1104 + difference 3 2) (sourceB1104 + difference 2 3) sourceC1104) = raw18518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18518; decide +kernel
    rw [ha]
    exact (canonical18518 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1104 + difference 3 4) (sourceB1104 + difference 4 3) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1104 + difference 3 4) (sourceB1104 + difference 4 3) sourceC1104) = raw18519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18519; decide +kernel
    rw [ha]
    exact (canonical18519 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1104 + difference 3 5) (sourceB1104 + difference 5 3) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1104 + difference 3 5) (sourceB1104 + difference 5 3) sourceC1104) = raw18520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18520; decide +kernel
    rw [ha]
    exact (canonical18520 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1104 + difference 4 0) (sourceB1104 + difference 0 4) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1104 + difference 4 0) (sourceB1104 + difference 0 4) sourceC1104) = raw18521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18521; decide +kernel
    rw [ha]
    exact (canonical18521 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1104 + difference 4 1) (sourceB1104 + difference 1 4) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1104 + difference 4 1) (sourceB1104 + difference 1 4) sourceC1104) = raw18425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18425; decide +kernel
    rw [ha]
    exact (canonical18425 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1104 + difference 4 2) (sourceB1104 + difference 2 4) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1104 + difference 4 2) (sourceB1104 + difference 2 4) sourceC1104) = raw18522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18522; decide +kernel
    rw [ha]
    exact (canonical18522 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1104 + difference 4 3) (sourceB1104 + difference 3 4) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1104 + difference 4 3) (sourceB1104 + difference 3 4) sourceC1104) = raw18523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18523; decide +kernel
    rw [ha]
    exact (canonical18523 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1104 + difference 4 5) (sourceB1104 + difference 5 4) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1104 + difference 4 5) (sourceB1104 + difference 5 4) sourceC1104) = raw18524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18524; decide +kernel
    rw [ha]
    exact (canonical18524 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1104 + difference 5 0) (sourceB1104 + difference 0 5) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA1104 + difference 5 0) (sourceB1104 + difference 0 5) sourceC1104) = raw18525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18525; decide +kernel
    rw [ha]
    exact (canonical18525 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1104 + difference 5 1) (sourceB1104 + difference 1 5) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1104 + difference 5 1) (sourceB1104 + difference 1 5) sourceC1104) = raw18430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18430; decide +kernel
    rw [ha]
    exact (canonical18430 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1104 + difference 5 2) (sourceB1104 + difference 2 5) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1104 + difference 5 2) (sourceB1104 + difference 2 5) sourceC1104) = raw18526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18526; decide +kernel
    rw [ha]
    exact (canonical18526 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1104 + difference 5 3) (sourceB1104 + difference 3 5) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1104 + difference 5 3) (sourceB1104 + difference 3 5) sourceC1104) = raw18527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18527; decide +kernel
    rw [ha]
    exact (canonical18527 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1104 + difference 5 4) (sourceB1104 + difference 4 5) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1104 + difference 5 4) (sourceB1104 + difference 4 5) sourceC1104) = raw18528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18528; decide +kernel
    rw [ha]
    exact (canonical18528 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1104 sourceB1104 sourceC1104
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1104, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1105 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1105 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC1105 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceForm1105 : Integer.Sparse Master := [(Sum.inr 5123, 3), (Sum.inr 5162, 1), (Sum.inr 5192, 3), (Sum.inr 5202, 1), (Sum.inr 5227, 1), (Sum.inr 5283, 1), (Sum.inr 5391, 3), (Sum.inr 5411, 6), (Sum.inr 5447, 1), (Sum.inr 5450, 3), (Sum.inr 5452, 3), (Sum.inr 5462, 1), (Sum.inr 5485, 3)]

theorem sourceEq1105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1105 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1105 + difference 0 1) (sourceB1105 + difference 1 0) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA1105 + difference 0 1) (sourceB1105 + difference 1 0) sourceC1105) = raw18529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18529; decide +kernel
    rw [ha]
    exact (canonical18529 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1105 + difference 0 2) (sourceB1105 + difference 2 0) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5462) := by
    have ha : (tripleCharges (sourceA1105 + difference 0 2) (sourceB1105 + difference 2 0) sourceC1105) = raw18530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18530; decide +kernel
    rw [ha]
    exact (canonical18530 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1105 + difference 0 3) (sourceB1105 + difference 3 0) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1105 + difference 0 3) (sourceB1105 + difference 3 0) sourceC1105) = raw18531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18531; decide +kernel
    rw [ha]
    exact (canonical18531 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1105 + difference 0 4) (sourceB1105 + difference 4 0) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1105 + difference 0 4) (sourceB1105 + difference 4 0) sourceC1105) = raw18532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18532; decide +kernel
    rw [ha]
    exact (canonical18532 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1105 + difference 0 5) (sourceB1105 + difference 5 0) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1105 + difference 0 5) (sourceB1105 + difference 5 0) sourceC1105) = raw18533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18533; decide +kernel
    rw [ha]
    exact (canonical18533 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1105 + difference 1 0) (sourceB1105 + difference 0 1) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA1105 + difference 1 0) (sourceB1105 + difference 0 1) sourceC1105) = raw18534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18534; decide +kernel
    rw [ha]
    exact (canonical18534 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1105 + difference 1 2) (sourceB1105 + difference 2 1) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1105 + difference 1 2) (sourceB1105 + difference 2 1) sourceC1105) = raw13376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13376; decide +kernel
    rw [ha]
    exact (canonical13376 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1105 + difference 1 3) (sourceB1105 + difference 3 1) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1105 + difference 1 3) (sourceB1105 + difference 3 1) sourceC1105) = raw13377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13377; decide +kernel
    rw [ha]
    exact (canonical13377 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1105 + difference 1 4) (sourceB1105 + difference 4 1) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1105 + difference 1 4) (sourceB1105 + difference 4 1) sourceC1105) = raw13378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13378; decide +kernel
    rw [ha]
    exact (canonical13378 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1105 + difference 1 5) (sourceB1105 + difference 5 1) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1105 + difference 1 5) (sourceB1105 + difference 5 1) sourceC1105) = raw13379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13379; decide +kernel
    rw [ha]
    exact (canonical13379 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1105 + difference 2 0) (sourceB1105 + difference 0 2) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA1105 + difference 2 0) (sourceB1105 + difference 0 2) sourceC1105) = raw13386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13386; decide +kernel
    rw [ha]
    exact (canonical13386 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1105 + difference 2 1) (sourceB1105 + difference 1 2) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA1105 + difference 2 1) (sourceB1105 + difference 1 2) sourceC1105) = raw18535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18535; decide +kernel
    rw [ha]
    exact (canonical18535 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1105 + difference 2 3) (sourceB1105 + difference 3 2) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1105 + difference 2 3) (sourceB1105 + difference 3 2) sourceC1105) = raw18536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18536; decide +kernel
    rw [ha]
    exact (canonical18536 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1105 + difference 2 4) (sourceB1105 + difference 4 2) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1105 + difference 2 4) (sourceB1105 + difference 4 2) sourceC1105) = raw18537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18537; decide +kernel
    rw [ha]
    exact (canonical18537 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1105 + difference 2 5) (sourceB1105 + difference 5 2) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1105 + difference 2 5) (sourceB1105 + difference 5 2) sourceC1105) = raw18538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18538; decide +kernel
    rw [ha]
    exact (canonical18538 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1105 + difference 3 0) (sourceB1105 + difference 0 3) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA1105 + difference 3 0) (sourceB1105 + difference 0 3) sourceC1105) = raw13391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13391; decide +kernel
    rw [ha]
    exact (canonical13391 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1105 + difference 3 1) (sourceB1105 + difference 1 3) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA1105 + difference 3 1) (sourceB1105 + difference 1 3) sourceC1105) = raw18539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18539; decide +kernel
    rw [ha]
    exact (canonical18539 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1105 + difference 3 2) (sourceB1105 + difference 2 3) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA1105 + difference 3 2) (sourceB1105 + difference 2 3) sourceC1105) = raw18540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18540; decide +kernel
    rw [ha]
    exact (canonical18540 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1105 + difference 3 4) (sourceB1105 + difference 4 3) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 3 4) (sourceB1105 + difference 4 3) sourceC1105) = raw18541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18541; decide +kernel
    rw [ha]
    exact (canonical18541 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1105 + difference 3 5) (sourceB1105 + difference 5 3) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 3 5) (sourceB1105 + difference 5 3) sourceC1105) = raw18542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18542; decide +kernel
    rw [ha]
    exact (canonical18542 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1105 + difference 4 0) (sourceB1105 + difference 0 4) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA1105 + difference 4 0) (sourceB1105 + difference 0 4) sourceC1105) = raw13396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13396; decide +kernel
    rw [ha]
    exact (canonical13396 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1105 + difference 4 1) (sourceB1105 + difference 1 4) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA1105 + difference 4 1) (sourceB1105 + difference 1 4) sourceC1105) = raw18543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18543; decide +kernel
    rw [ha]
    exact (canonical18543 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1105 + difference 4 2) (sourceB1105 + difference 2 4) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA1105 + difference 4 2) (sourceB1105 + difference 2 4) sourceC1105) = raw18544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18544; decide +kernel
    rw [ha]
    exact (canonical18544 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1105 + difference 4 3) (sourceB1105 + difference 3 4) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 4 3) (sourceB1105 + difference 3 4) sourceC1105) = raw18545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18545; decide +kernel
    rw [ha]
    exact (canonical18545 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1105 + difference 4 5) (sourceB1105 + difference 5 4) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 4 5) (sourceB1105 + difference 5 4) sourceC1105) = raw18546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18546; decide +kernel
    rw [ha]
    exact (canonical18546 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1105 + difference 5 0) (sourceB1105 + difference 0 5) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA1105 + difference 5 0) (sourceB1105 + difference 0 5) sourceC1105) = raw13401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw13401; decide +kernel
    rw [ha]
    exact (canonical13401 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1105 + difference 5 1) (sourceB1105 + difference 1 5) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA1105 + difference 5 1) (sourceB1105 + difference 1 5) sourceC1105) = raw18547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18547; decide +kernel
    rw [ha]
    exact (canonical18547 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1105 + difference 5 2) (sourceB1105 + difference 2 5) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA1105 + difference 5 2) (sourceB1105 + difference 2 5) sourceC1105) = raw18548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18548; decide +kernel
    rw [ha]
    exact (canonical18548 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1105 + difference 5 3) (sourceB1105 + difference 3 5) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 5 3) (sourceB1105 + difference 3 5) sourceC1105) = raw18549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18549; decide +kernel
    rw [ha]
    exact (canonical18549 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1105 + difference 5 4) (sourceB1105 + difference 4 5) sourceC1105) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1105 + difference 5 4) (sourceB1105 + difference 4 5) sourceC1105) = raw18550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1105 sourceB1105 sourceC1105 difference raw18550; decide +kernel
    rw [ha]
    exact (canonical18550 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1105 sourceB1105 sourceC1105
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1105, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1106 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1106 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC1106 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceForm1106 : Integer.Sparse Master := [(Sum.inr 2853, 3), (Sum.inr 2880, 1), (Sum.inr 3076, 1), (Sum.inr 3370, 3), (Sum.inr 3390, 1), (Sum.inr 3563, 1), (Sum.inr 3778, 3), (Sum.inr 3809, 6), (Sum.inr 4007, 1), (Sum.inr 4010, 3), (Sum.inr 4025, 1), (Sum.inr 4029, 3), (Sum.inr 4039, 3)]

theorem sourceEq1106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1106 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1106 + difference 0 1) (sourceB1106 + difference 1 0) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3563) := by
    have ha : (tripleCharges (sourceA1106 + difference 0 1) (sourceB1106 + difference 1 0) sourceC1106) = raw18551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18551; decide +kernel
    rw [ha]
    exact (canonical18551 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1106 + difference 0 2) (sourceB1106 + difference 2 0) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4007) := by
    have ha : (tripleCharges (sourceA1106 + difference 0 2) (sourceB1106 + difference 2 0) sourceC1106) = raw18552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18552; decide +kernel
    rw [ha]
    exact (canonical18552 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1106 + difference 0 3) (sourceB1106 + difference 3 0) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA1106 + difference 0 3) (sourceB1106 + difference 3 0) sourceC1106) = raw18553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18553; decide +kernel
    rw [ha]
    exact (canonical18553 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1106 + difference 0 4) (sourceB1106 + difference 4 0) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA1106 + difference 0 4) (sourceB1106 + difference 4 0) sourceC1106) = raw18554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18554; decide +kernel
    rw [ha]
    exact (canonical18554 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1106 + difference 0 5) (sourceB1106 + difference 5 0) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA1106 + difference 0 5) (sourceB1106 + difference 5 0) sourceC1106) = raw18555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18555; decide +kernel
    rw [ha]
    exact (canonical18555 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1106 + difference 1 0) (sourceB1106 + difference 0 1) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3076) := by
    have ha : (tripleCharges (sourceA1106 + difference 1 0) (sourceB1106 + difference 0 1) sourceC1106) = raw18556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18556; decide +kernel
    rw [ha]
    exact (canonical18556 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1106 + difference 1 2) (sourceB1106 + difference 2 1) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA1106 + difference 1 2) (sourceB1106 + difference 2 1) sourceC1106) = raw13406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw13406; decide +kernel
    rw [ha]
    exact (canonical13406 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1106 + difference 1 3) (sourceB1106 + difference 3 1) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA1106 + difference 1 3) (sourceB1106 + difference 3 1) sourceC1106) = raw13407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw13407; decide +kernel
    rw [ha]
    exact (canonical13407 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1106 + difference 1 4) (sourceB1106 + difference 4 1) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA1106 + difference 1 4) (sourceB1106 + difference 4 1) sourceC1106) = raw13408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw13408; decide +kernel
    rw [ha]
    exact (canonical13408 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1106 + difference 1 5) (sourceB1106 + difference 5 1) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA1106 + difference 1 5) (sourceB1106 + difference 5 1) sourceC1106) = raw13409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw13409; decide +kernel
    rw [ha]
    exact (canonical13409 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1106 + difference 2 0) (sourceB1106 + difference 0 2) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA1106 + difference 2 0) (sourceB1106 + difference 0 2) sourceC1106) = raw13416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw13416; decide +kernel
    rw [ha]
    exact (canonical13416 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1106 + difference 2 1) (sourceB1106 + difference 1 2) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3390) := by
    have ha : (tripleCharges (sourceA1106 + difference 2 1) (sourceB1106 + difference 1 2) sourceC1106) = raw18557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18557; decide +kernel
    rw [ha]
    exact (canonical18557 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1106 + difference 2 3) (sourceB1106 + difference 3 2) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA1106 + difference 2 3) (sourceB1106 + difference 3 2) sourceC1106) = raw18558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18558; decide +kernel
    rw [ha]
    exact (canonical18558 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1106 + difference 2 4) (sourceB1106 + difference 4 2) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA1106 + difference 2 4) (sourceB1106 + difference 4 2) sourceC1106) = raw18559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18559; decide +kernel
    rw [ha]
    exact (canonical18559 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1106 + difference 2 5) (sourceB1106 + difference 5 2) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA1106 + difference 2 5) (sourceB1106 + difference 5 2) sourceC1106) = raw18560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18560; decide +kernel
    rw [ha]
    exact (canonical18560 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1106 + difference 3 0) (sourceB1106 + difference 0 3) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA1106 + difference 3 0) (sourceB1106 + difference 0 3) sourceC1106) = raw13421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw13421; decide +kernel
    rw [ha]
    exact (canonical13421 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1106 + difference 3 1) (sourceB1106 + difference 1 3) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3370) := by
    have ha : (tripleCharges (sourceA1106 + difference 3 1) (sourceB1106 + difference 1 3) sourceC1106) = raw18561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18561; decide +kernel
    rw [ha]
    exact (canonical18561 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1106 + difference 3 2) (sourceB1106 + difference 2 3) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3778) := by
    have ha : (tripleCharges (sourceA1106 + difference 3 2) (sourceB1106 + difference 2 3) sourceC1106) = raw18562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18562; decide +kernel
    rw [ha]
    exact (canonical18562 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1106 + difference 3 4) (sourceB1106 + difference 4 3) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1106 + difference 3 4) (sourceB1106 + difference 4 3) sourceC1106) = raw18563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18563; decide +kernel
    rw [ha]
    exact (canonical18563 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1106 + difference 3 5) (sourceB1106 + difference 5 3) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1106 + difference 3 5) (sourceB1106 + difference 5 3) sourceC1106) = raw18564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18564; decide +kernel
    rw [ha]
    exact (canonical18564 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1106 + difference 4 0) (sourceB1106 + difference 0 4) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA1106 + difference 4 0) (sourceB1106 + difference 0 4) sourceC1106) = raw13426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw13426; decide +kernel
    rw [ha]
    exact (canonical13426 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1106 + difference 4 1) (sourceB1106 + difference 1 4) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3370) := by
    have ha : (tripleCharges (sourceA1106 + difference 4 1) (sourceB1106 + difference 1 4) sourceC1106) = raw18565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18565; decide +kernel
    rw [ha]
    exact (canonical18565 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1106 + difference 4 2) (sourceB1106 + difference 2 4) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3778) := by
    have ha : (tripleCharges (sourceA1106 + difference 4 2) (sourceB1106 + difference 2 4) sourceC1106) = raw18566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18566; decide +kernel
    rw [ha]
    exact (canonical18566 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1106 + difference 4 3) (sourceB1106 + difference 3 4) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1106 + difference 4 3) (sourceB1106 + difference 3 4) sourceC1106) = raw18567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18567; decide +kernel
    rw [ha]
    exact (canonical18567 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1106 + difference 4 5) (sourceB1106 + difference 5 4) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1106 + difference 4 5) (sourceB1106 + difference 5 4) sourceC1106) = raw18568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18568; decide +kernel
    rw [ha]
    exact (canonical18568 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1106 + difference 5 0) (sourceB1106 + difference 0 5) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA1106 + difference 5 0) (sourceB1106 + difference 0 5) sourceC1106) = raw13431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw13431; decide +kernel
    rw [ha]
    exact (canonical13431 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1106 + difference 5 1) (sourceB1106 + difference 1 5) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3370) := by
    have ha : (tripleCharges (sourceA1106 + difference 5 1) (sourceB1106 + difference 1 5) sourceC1106) = raw18569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18569; decide +kernel
    rw [ha]
    exact (canonical18569 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1106 + difference 5 2) (sourceB1106 + difference 2 5) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3778) := by
    have ha : (tripleCharges (sourceA1106 + difference 5 2) (sourceB1106 + difference 2 5) sourceC1106) = raw18570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18570; decide +kernel
    rw [ha]
    exact (canonical18570 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1106 + difference 5 3) (sourceB1106 + difference 3 5) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1106 + difference 5 3) (sourceB1106 + difference 3 5) sourceC1106) = raw18571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18571; decide +kernel
    rw [ha]
    exact (canonical18571 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1106 + difference 5 4) (sourceB1106 + difference 4 5) sourceC1106) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1106 + difference 5 4) (sourceB1106 + difference 4 5) sourceC1106) = raw18572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1106 sourceB1106 sourceC1106 difference raw18572; decide +kernel
    rw [ha]
    exact (canonical18572 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1106 sourceB1106 sourceC1106
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1106, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1107 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1107 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1107 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceForm1107 : Integer.Sparse Master := [(Sum.inr 4851, 3), (Sum.inr 4863, 1), (Sum.inr 4885, 1), (Sum.inr 5380, 3), (Sum.inr 5383, 1), (Sum.inr 5406, 3), (Sum.inr 5422, 3), (Sum.inr 5427, 1), (Sum.inr 5429, 3), (Sum.inr 5430, 6), (Sum.inr 5437, 1), (Sum.inr 5479, 1), (Sum.inr 5482, 3)]

theorem sourceEq1107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1107 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1107 + difference 0 1) (sourceB1107 + difference 1 0) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA1107 + difference 0 1) (sourceB1107 + difference 1 0) sourceC1107) = raw18573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18573; decide +kernel
    rw [ha]
    exact (canonical18573 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1107 + difference 0 2) (sourceB1107 + difference 2 0) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5479) := by
    have ha : (tripleCharges (sourceA1107 + difference 0 2) (sourceB1107 + difference 2 0) sourceC1107) = raw18574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18574; decide +kernel
    rw [ha]
    exact (canonical18574 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1107 + difference 0 3) (sourceB1107 + difference 3 0) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1107 + difference 0 3) (sourceB1107 + difference 3 0) sourceC1107) = raw18575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18575; decide +kernel
    rw [ha]
    exact (canonical18575 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1107 + difference 0 4) (sourceB1107 + difference 4 0) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1107 + difference 0 4) (sourceB1107 + difference 4 0) sourceC1107) = raw18576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18576; decide +kernel
    rw [ha]
    exact (canonical18576 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1107 + difference 0 5) (sourceB1107 + difference 5 0) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1107 + difference 0 5) (sourceB1107 + difference 5 0) sourceC1107) = raw18577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18577; decide +kernel
    rw [ha]
    exact (canonical18577 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1107 + difference 1 0) (sourceB1107 + difference 0 1) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA1107 + difference 1 0) (sourceB1107 + difference 0 1) sourceC1107) = raw18578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18578; decide +kernel
    rw [ha]
    exact (canonical18578 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1107 + difference 1 2) (sourceB1107 + difference 2 1) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA1107 + difference 1 2) (sourceB1107 + difference 2 1) sourceC1107) = raw18579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18579; decide +kernel
    rw [ha]
    exact (canonical18579 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1107 + difference 1 3) (sourceB1107 + difference 3 1) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1107 + difference 1 3) (sourceB1107 + difference 3 1) sourceC1107) = raw18580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18580; decide +kernel
    rw [ha]
    exact (canonical18580 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1107 + difference 1 4) (sourceB1107 + difference 4 1) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1107 + difference 1 4) (sourceB1107 + difference 4 1) sourceC1107) = raw18581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18581; decide +kernel
    rw [ha]
    exact (canonical18581 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1107 + difference 1 5) (sourceB1107 + difference 5 1) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1107 + difference 1 5) (sourceB1107 + difference 5 1) sourceC1107) = raw18582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18582; decide +kernel
    rw [ha]
    exact (canonical18582 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1107 + difference 2 0) (sourceB1107 + difference 0 2) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA1107 + difference 2 0) (sourceB1107 + difference 0 2) sourceC1107) = raw18583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18583; decide +kernel
    rw [ha]
    exact (canonical18583 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1107 + difference 2 1) (sourceB1107 + difference 1 2) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA1107 + difference 2 1) (sourceB1107 + difference 1 2) sourceC1107) = raw18584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18584; decide +kernel
    rw [ha]
    exact (canonical18584 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1107 + difference 2 3) (sourceB1107 + difference 3 2) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1107 + difference 2 3) (sourceB1107 + difference 3 2) sourceC1107) = raw18585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18585; decide +kernel
    rw [ha]
    exact (canonical18585 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1107 + difference 2 4) (sourceB1107 + difference 4 2) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1107 + difference 2 4) (sourceB1107 + difference 4 2) sourceC1107) = raw18586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18586; decide +kernel
    rw [ha]
    exact (canonical18586 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1107 + difference 2 5) (sourceB1107 + difference 5 2) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1107 + difference 2 5) (sourceB1107 + difference 5 2) sourceC1107) = raw18587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18587; decide +kernel
    rw [ha]
    exact (canonical18587 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1107 + difference 3 0) (sourceB1107 + difference 0 3) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA1107 + difference 3 0) (sourceB1107 + difference 0 3) sourceC1107) = raw18588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18588; decide +kernel
    rw [ha]
    exact (canonical18588 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1107 + difference 3 1) (sourceB1107 + difference 1 3) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1107 + difference 3 1) (sourceB1107 + difference 1 3) sourceC1107) = raw18589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18589; decide +kernel
    rw [ha]
    exact (canonical18589 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1107 + difference 3 2) (sourceB1107 + difference 2 3) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1107 + difference 3 2) (sourceB1107 + difference 2 3) sourceC1107) = raw18590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18590; decide +kernel
    rw [ha]
    exact (canonical18590 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1107 + difference 3 4) (sourceB1107 + difference 4 3) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 3 4) (sourceB1107 + difference 4 3) sourceC1107) = raw18591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18591; decide +kernel
    rw [ha]
    exact (canonical18591 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1107 + difference 3 5) (sourceB1107 + difference 5 3) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 3 5) (sourceB1107 + difference 5 3) sourceC1107) = raw18592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18592; decide +kernel
    rw [ha]
    exact (canonical18592 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1107 + difference 4 0) (sourceB1107 + difference 0 4) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA1107 + difference 4 0) (sourceB1107 + difference 0 4) sourceC1107) = raw18593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18593; decide +kernel
    rw [ha]
    exact (canonical18593 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1107 + difference 4 1) (sourceB1107 + difference 1 4) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1107 + difference 4 1) (sourceB1107 + difference 1 4) sourceC1107) = raw18594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18594; decide +kernel
    rw [ha]
    exact (canonical18594 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1107 + difference 4 2) (sourceB1107 + difference 2 4) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1107 + difference 4 2) (sourceB1107 + difference 2 4) sourceC1107) = raw18595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18595; decide +kernel
    rw [ha]
    exact (canonical18595 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1107 + difference 4 3) (sourceB1107 + difference 3 4) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 4 3) (sourceB1107 + difference 3 4) sourceC1107) = raw18596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18596; decide +kernel
    rw [ha]
    exact (canonical18596 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1107 + difference 4 5) (sourceB1107 + difference 5 4) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 4 5) (sourceB1107 + difference 5 4) sourceC1107) = raw18597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18597; decide +kernel
    rw [ha]
    exact (canonical18597 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1107 + difference 5 0) (sourceB1107 + difference 0 5) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA1107 + difference 5 0) (sourceB1107 + difference 0 5) sourceC1107) = raw18598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18598; decide +kernel
    rw [ha]
    exact (canonical18598 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1107 + difference 5 1) (sourceB1107 + difference 1 5) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1107 + difference 5 1) (sourceB1107 + difference 1 5) sourceC1107) = raw18599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18599; decide +kernel
    rw [ha]
    exact (canonical18599 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1107 + difference 5 2) (sourceB1107 + difference 2 5) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1107 + difference 5 2) (sourceB1107 + difference 2 5) sourceC1107) = raw18600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18600; decide +kernel
    rw [ha]
    exact (canonical18600 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1107 + difference 5 3) (sourceB1107 + difference 3 5) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 5 3) (sourceB1107 + difference 3 5) sourceC1107) = raw18601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18601; decide +kernel
    rw [ha]
    exact (canonical18601 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1107 + difference 5 4) (sourceB1107 + difference 4 5) sourceC1107) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1107 + difference 5 4) (sourceB1107 + difference 4 5) sourceC1107) = raw18602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1107 sourceB1107 sourceC1107 difference raw18602; decide +kernel
    rw [ha]
    exact (canonical18602 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1107 sourceB1107 sourceC1107
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1107, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1108 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB1108 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1108 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceForm1108 : Integer.Sparse Master := [(Sum.inr 5085, 3), (Sum.inr 5097, 1), (Sum.inr 5277, 1), (Sum.inr 5281, 3), (Sum.inr 5301, 1), (Sum.inr 5359, 3), (Sum.inr 5433, 3), (Sum.inr 5437, 1), (Sum.inr 5445, 6), (Sum.inr 5450, 3), (Sum.inr 5469, 3), (Sum.inr 5474, 1), (Sum.inr 5479, 1)]

theorem sourceEq1108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1108 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1108 + difference 0 1) (sourceB1108 + difference 1 0) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5479) := by
    have ha : (tripleCharges (sourceA1108 + difference 0 1) (sourceB1108 + difference 1 0) sourceC1108) = raw18407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18407; decide +kernel
    rw [ha]
    exact (canonical18407 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1108 + difference 0 2) (sourceB1108 + difference 2 0) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA1108 + difference 0 2) (sourceB1108 + difference 2 0) sourceC1108) = raw18510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18510; decide +kernel
    rw [ha]
    exact (canonical18510 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1108 + difference 0 3) (sourceB1108 + difference 3 0) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1108 + difference 0 3) (sourceB1108 + difference 3 0) sourceC1108) = raw18603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18603; decide +kernel
    rw [ha]
    exact (canonical18603 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1108 + difference 0 4) (sourceB1108 + difference 4 0) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1108 + difference 0 4) (sourceB1108 + difference 4 0) sourceC1108) = raw18604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18604; decide +kernel
    rw [ha]
    exact (canonical18604 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1108 + difference 0 5) (sourceB1108 + difference 5 0) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1108 + difference 0 5) (sourceB1108 + difference 5 0) sourceC1108) = raw18605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18605; decide +kernel
    rw [ha]
    exact (canonical18605 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1108 + difference 1 0) (sourceB1108 + difference 0 1) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5097) := by
    have ha : (tripleCharges (sourceA1108 + difference 1 0) (sourceB1108 + difference 0 1) sourceC1108) = raw18606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18606; decide +kernel
    rw [ha]
    exact (canonical18606 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1108 + difference 1 2) (sourceB1108 + difference 2 1) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA1108 + difference 1 2) (sourceB1108 + difference 2 1) sourceC1108) = raw18515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18515; decide +kernel
    rw [ha]
    exact (canonical18515 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1108 + difference 1 3) (sourceB1108 + difference 3 1) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA1108 + difference 1 3) (sourceB1108 + difference 3 1) sourceC1108) = raw18607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18607; decide +kernel
    rw [ha]
    exact (canonical18607 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1108 + difference 1 4) (sourceB1108 + difference 4 1) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA1108 + difference 1 4) (sourceB1108 + difference 4 1) sourceC1108) = raw18608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18608; decide +kernel
    rw [ha]
    exact (canonical18608 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1108 + difference 1 5) (sourceB1108 + difference 5 1) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA1108 + difference 1 5) (sourceB1108 + difference 5 1) sourceC1108) = raw18609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18609; decide +kernel
    rw [ha]
    exact (canonical18609 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1108 + difference 2 0) (sourceB1108 + difference 0 2) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5277) := by
    have ha : (tripleCharges (sourceA1108 + difference 2 0) (sourceB1108 + difference 0 2) sourceC1108) = raw18610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18610; decide +kernel
    rw [ha]
    exact (canonical18610 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1108 + difference 2 1) (sourceB1108 + difference 1 2) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA1108 + difference 2 1) (sourceB1108 + difference 1 2) sourceC1108) = raw18417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18417; decide +kernel
    rw [ha]
    exact (canonical18417 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1108 + difference 2 3) (sourceB1108 + difference 3 2) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1108 + difference 2 3) (sourceB1108 + difference 3 2) sourceC1108) = raw18611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18611; decide +kernel
    rw [ha]
    exact (canonical18611 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1108 + difference 2 4) (sourceB1108 + difference 4 2) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1108 + difference 2 4) (sourceB1108 + difference 4 2) sourceC1108) = raw18612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18612; decide +kernel
    rw [ha]
    exact (canonical18612 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1108 + difference 2 5) (sourceB1108 + difference 5 2) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1108 + difference 2 5) (sourceB1108 + difference 5 2) sourceC1108) = raw18613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18613; decide +kernel
    rw [ha]
    exact (canonical18613 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1108 + difference 3 0) (sourceB1108 + difference 0 3) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1108 + difference 3 0) (sourceB1108 + difference 0 3) sourceC1108) = raw18614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18614; decide +kernel
    rw [ha]
    exact (canonical18614 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1108 + difference 3 1) (sourceB1108 + difference 1 3) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1108 + difference 3 1) (sourceB1108 + difference 1 3) sourceC1108) = raw18422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18422; decide +kernel
    rw [ha]
    exact (canonical18422 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1108 + difference 3 2) (sourceB1108 + difference 2 3) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1108 + difference 3 2) (sourceB1108 + difference 2 3) sourceC1108) = raw18520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18520; decide +kernel
    rw [ha]
    exact (canonical18520 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1108 + difference 3 4) (sourceB1108 + difference 4 3) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 3 4) (sourceB1108 + difference 4 3) sourceC1108) = raw18615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18615; decide +kernel
    rw [ha]
    exact (canonical18615 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1108 + difference 3 5) (sourceB1108 + difference 5 3) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 3 5) (sourceB1108 + difference 5 3) sourceC1108) = raw18616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18616; decide +kernel
    rw [ha]
    exact (canonical18616 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1108 + difference 4 0) (sourceB1108 + difference 0 4) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1108 + difference 4 0) (sourceB1108 + difference 0 4) sourceC1108) = raw18617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18617; decide +kernel
    rw [ha]
    exact (canonical18617 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1108 + difference 4 1) (sourceB1108 + difference 1 4) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1108 + difference 4 1) (sourceB1108 + difference 1 4) sourceC1108) = raw18427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18427; decide +kernel
    rw [ha]
    exact (canonical18427 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1108 + difference 4 2) (sourceB1108 + difference 2 4) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1108 + difference 4 2) (sourceB1108 + difference 2 4) sourceC1108) = raw18524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18524; decide +kernel
    rw [ha]
    exact (canonical18524 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1108 + difference 4 3) (sourceB1108 + difference 3 4) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 4 3) (sourceB1108 + difference 3 4) sourceC1108) = raw18618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18618; decide +kernel
    rw [ha]
    exact (canonical18618 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1108 + difference 4 5) (sourceB1108 + difference 5 4) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 4 5) (sourceB1108 + difference 5 4) sourceC1108) = raw18619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18619; decide +kernel
    rw [ha]
    exact (canonical18619 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1108 + difference 5 0) (sourceB1108 + difference 0 5) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1108 + difference 5 0) (sourceB1108 + difference 0 5) sourceC1108) = raw18408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18408; decide +kernel
    rw [ha]
    exact (canonical18408 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1108 + difference 5 1) (sourceB1108 + difference 1 5) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1108 + difference 5 1) (sourceB1108 + difference 1 5) sourceC1108) = raw18516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18516; decide +kernel
    rw [ha]
    exact (canonical18516 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1108 + difference 5 2) (sourceB1108 + difference 2 5) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1108 + difference 5 2) (sourceB1108 + difference 2 5) sourceC1108) = raw18409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18409; decide +kernel
    rw [ha]
    exact (canonical18409 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1108 + difference 5 3) (sourceB1108 + difference 3 5) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 5 3) (sourceB1108 + difference 3 5) sourceC1108) = raw18410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18410; decide +kernel
    rw [ha]
    exact (canonical18410 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1108 + difference 5 4) (sourceB1108 + difference 4 5) sourceC1108) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1108 + difference 5 4) (sourceB1108 + difference 4 5) sourceC1108) = raw18411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1108 sourceB1108 sourceC1108 difference raw18411; decide +kernel
    rw [ha]
    exact (canonical18411 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1108 sourceB1108 sourceC1108
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1108, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1109 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB1109 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1109 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceForm1109 : Integer.Sparse Master := [(Sum.inr 3058, 1), (Sum.inr 3059, 1), (Sum.inr 3074, 3), (Sum.inr 3461, 3), (Sum.inr 3619, 1), (Sum.inr 3759, 3), (Sum.inr 3899, 1), (Sum.inr 3952, 3), (Sum.inr 3962, 1), (Sum.inr 3975, 1), (Sum.inr 4024, 6), (Sum.inr 4029, 3), (Sum.inr 4033, 3)]

theorem sourceEq1109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1109 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1109 + difference 0 1) (sourceB1109 + difference 1 0) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3975) := by
    have ha : (tripleCharges (sourceA1109 + difference 0 1) (sourceB1109 + difference 1 0) sourceC1109) = raw18620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18620; decide +kernel
    rw [ha]
    exact (canonical18620 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1109 + difference 0 2) (sourceB1109 + difference 2 0) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3962) := by
    have ha : (tripleCharges (sourceA1109 + difference 0 2) (sourceB1109 + difference 2 0) sourceC1109) = raw18621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18621; decide +kernel
    rw [ha]
    exact (canonical18621 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1109 + difference 0 3) (sourceB1109 + difference 3 0) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3952) := by
    have ha : (tripleCharges (sourceA1109 + difference 0 3) (sourceB1109 + difference 3 0) sourceC1109) = raw18622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18622; decide +kernel
    rw [ha]
    exact (canonical18622 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1109 + difference 0 4) (sourceB1109 + difference 4 0) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3952) := by
    have ha : (tripleCharges (sourceA1109 + difference 0 4) (sourceB1109 + difference 4 0) sourceC1109) = raw18623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18623; decide +kernel
    rw [ha]
    exact (canonical18623 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1109 + difference 0 5) (sourceB1109 + difference 5 0) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3952) := by
    have ha : (tripleCharges (sourceA1109 + difference 0 5) (sourceB1109 + difference 5 0) sourceC1109) = raw18624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18624; decide +kernel
    rw [ha]
    exact (canonical18624 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1109 + difference 1 0) (sourceB1109 + difference 0 1) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA1109 + difference 1 0) (sourceB1109 + difference 0 1) sourceC1109) = raw18625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18625; decide +kernel
    rw [ha]
    exact (canonical18625 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1109 + difference 1 2) (sourceB1109 + difference 2 1) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA1109 + difference 1 2) (sourceB1109 + difference 2 1) sourceC1109) = raw18626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18626; decide +kernel
    rw [ha]
    exact (canonical18626 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1109 + difference 1 3) (sourceB1109 + difference 3 1) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA1109 + difference 1 3) (sourceB1109 + difference 3 1) sourceC1109) = raw18627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18627; decide +kernel
    rw [ha]
    exact (canonical18627 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1109 + difference 1 4) (sourceB1109 + difference 4 1) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA1109 + difference 1 4) (sourceB1109 + difference 4 1) sourceC1109) = raw18628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18628; decide +kernel
    rw [ha]
    exact (canonical18628 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1109 + difference 1 5) (sourceB1109 + difference 5 1) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA1109 + difference 1 5) (sourceB1109 + difference 5 1) sourceC1109) = raw18629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18629; decide +kernel
    rw [ha]
    exact (canonical18629 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1109 + difference 2 0) (sourceB1109 + difference 0 2) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA1109 + difference 2 0) (sourceB1109 + difference 0 2) sourceC1109) = raw18630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18630; decide +kernel
    rw [ha]
    exact (canonical18630 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1109 + difference 2 1) (sourceB1109 + difference 1 2) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA1109 + difference 2 1) (sourceB1109 + difference 1 2) sourceC1109) = raw18631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18631; decide +kernel
    rw [ha]
    exact (canonical18631 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1109 + difference 2 3) (sourceB1109 + difference 3 2) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA1109 + difference 2 3) (sourceB1109 + difference 3 2) sourceC1109) = raw18632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18632; decide +kernel
    rw [ha]
    exact (canonical18632 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1109 + difference 2 4) (sourceB1109 + difference 4 2) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA1109 + difference 2 4) (sourceB1109 + difference 4 2) sourceC1109) = raw18633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18633; decide +kernel
    rw [ha]
    exact (canonical18633 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1109 + difference 2 5) (sourceB1109 + difference 5 2) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA1109 + difference 2 5) (sourceB1109 + difference 5 2) sourceC1109) = raw18634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18634; decide +kernel
    rw [ha]
    exact (canonical18634 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1109 + difference 3 0) (sourceB1109 + difference 0 3) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA1109 + difference 3 0) (sourceB1109 + difference 0 3) sourceC1109) = raw18635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18635; decide +kernel
    rw [ha]
    exact (canonical18635 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1109 + difference 3 1) (sourceB1109 + difference 1 3) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA1109 + difference 3 1) (sourceB1109 + difference 1 3) sourceC1109) = raw18636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18636; decide +kernel
    rw [ha]
    exact (canonical18636 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1109 + difference 3 2) (sourceB1109 + difference 2 3) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA1109 + difference 3 2) (sourceB1109 + difference 2 3) sourceC1109) = raw18637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18637; decide +kernel
    rw [ha]
    exact (canonical18637 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1109 + difference 3 4) (sourceB1109 + difference 4 3) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA1109 + difference 3 4) (sourceB1109 + difference 4 3) sourceC1109) = raw18638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18638; decide +kernel
    rw [ha]
    exact (canonical18638 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1109 + difference 3 5) (sourceB1109 + difference 5 3) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA1109 + difference 3 5) (sourceB1109 + difference 5 3) sourceC1109) = raw18639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18639; decide +kernel
    rw [ha]
    exact (canonical18639 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1109 + difference 4 0) (sourceB1109 + difference 0 4) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA1109 + difference 4 0) (sourceB1109 + difference 0 4) sourceC1109) = raw18640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18640; decide +kernel
    rw [ha]
    exact (canonical18640 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1109 + difference 4 1) (sourceB1109 + difference 1 4) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA1109 + difference 4 1) (sourceB1109 + difference 1 4) sourceC1109) = raw18641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18641; decide +kernel
    rw [ha]
    exact (canonical18641 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1109 + difference 4 2) (sourceB1109 + difference 2 4) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA1109 + difference 4 2) (sourceB1109 + difference 2 4) sourceC1109) = raw18642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18642; decide +kernel
    rw [ha]
    exact (canonical18642 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1109 + difference 4 3) (sourceB1109 + difference 3 4) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA1109 + difference 4 3) (sourceB1109 + difference 3 4) sourceC1109) = raw18643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18643; decide +kernel
    rw [ha]
    exact (canonical18643 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1109 + difference 4 5) (sourceB1109 + difference 5 4) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA1109 + difference 4 5) (sourceB1109 + difference 5 4) sourceC1109) = raw18644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18644; decide +kernel
    rw [ha]
    exact (canonical18644 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1109 + difference 5 0) (sourceB1109 + difference 0 5) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA1109 + difference 5 0) (sourceB1109 + difference 0 5) sourceC1109) = raw18645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18645; decide +kernel
    rw [ha]
    exact (canonical18645 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1109 + difference 5 1) (sourceB1109 + difference 1 5) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA1109 + difference 5 1) (sourceB1109 + difference 1 5) sourceC1109) = raw18646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18646; decide +kernel
    rw [ha]
    exact (canonical18646 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1109 + difference 5 2) (sourceB1109 + difference 2 5) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA1109 + difference 5 2) (sourceB1109 + difference 2 5) sourceC1109) = raw18647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18647; decide +kernel
    rw [ha]
    exact (canonical18647 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1109 + difference 5 3) (sourceB1109 + difference 3 5) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA1109 + difference 5 3) (sourceB1109 + difference 3 5) sourceC1109) = raw18648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18648; decide +kernel
    rw [ha]
    exact (canonical18648 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1109 + difference 5 4) (sourceB1109 + difference 4 5) sourceC1109) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA1109 + difference 5 4) (sourceB1109 + difference 4 5) sourceC1109) = raw18649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1109 sourceB1109 sourceC1109 difference raw18649; decide +kernel
    rw [ha]
    exact (canonical18649 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1109 sourceB1109 sourceC1109
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1109, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1110 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1110 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1110 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm1110 : Integer.Sparse Master := [(Sum.inr 5162, 1), (Sum.inr 5163, 2), (Sum.inr 5172, 1), (Sum.inr 5290, 1), (Sum.inr 5401, 2), (Sum.inr 5404, 2), (Sum.inr 5411, 2), (Sum.inr 5416, 1), (Sum.inr 5418, 1), (Sum.inr 5442, 2), (Sum.inr 5447, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 2), (Sum.inr 5452, 1), (Sum.inr 5462, 1), (Sum.inr 5481, 1), (Sum.inr 5485, 3), (Sum.inr 5489, 1), (Sum.inr 5492, 2), (Sum.inr 5493, 2)]

theorem sourceEq1110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1110 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1110 + difference 0 1) (sourceB1110 + difference 1 0) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1110 + difference 0 1) (sourceB1110 + difference 1 0) sourceC1110) = raw18650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18650; decide +kernel
    rw [ha]
    exact (canonical18650 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1110 + difference 0 2) (sourceB1110 + difference 2 0) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1110 + difference 0 2) (sourceB1110 + difference 2 0) sourceC1110) = raw18651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18651; decide +kernel
    rw [ha]
    exact (canonical18651 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1110 + difference 0 3) (sourceB1110 + difference 3 0) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1110 + difference 0 3) (sourceB1110 + difference 3 0) sourceC1110) = raw3029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw3029; decide +kernel
    rw [ha]
    exact (canonical3029 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1110 + difference 0 4) (sourceB1110 + difference 4 0) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1110 + difference 0 4) (sourceB1110 + difference 4 0) sourceC1110) = raw18652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18652; decide +kernel
    rw [ha]
    exact (canonical18652 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1110 + difference 0 5) (sourceB1110 + difference 5 0) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1110 + difference 0 5) (sourceB1110 + difference 5 0) sourceC1110) = raw18653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18653; decide +kernel
    rw [ha]
    exact (canonical18653 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1110 + difference 1 0) (sourceB1110 + difference 0 1) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1110 + difference 1 0) (sourceB1110 + difference 0 1) sourceC1110) = raw3044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw3044; decide +kernel
    rw [ha]
    exact (canonical3044 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1110 + difference 1 2) (sourceB1110 + difference 2 1) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1110 + difference 1 2) (sourceB1110 + difference 2 1) sourceC1110) = raw3046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw3046; decide +kernel
    rw [ha]
    exact (canonical3046 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1110 + difference 1 3) (sourceB1110 + difference 3 1) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1110 + difference 1 3) (sourceB1110 + difference 3 1) sourceC1110) = raw13573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw13573; decide +kernel
    rw [ha]
    exact (canonical13573 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1110 + difference 1 4) (sourceB1110 + difference 4 1) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1110 + difference 1 4) (sourceB1110 + difference 4 1) sourceC1110) = raw3047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw3047; decide +kernel
    rw [ha]
    exact (canonical3047 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1110 + difference 1 5) (sourceB1110 + difference 5 1) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1110 + difference 1 5) (sourceB1110 + difference 5 1) sourceC1110) = raw3048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw3048; decide +kernel
    rw [ha]
    exact (canonical3048 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1110 + difference 2 0) (sourceB1110 + difference 0 2) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA1110 + difference 2 0) (sourceB1110 + difference 0 2) sourceC1110) = raw13579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw13579; decide +kernel
    rw [ha]
    exact (canonical13579 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1110 + difference 2 1) (sourceB1110 + difference 1 2) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5462) := by
    have ha : (tripleCharges (sourceA1110 + difference 2 1) (sourceB1110 + difference 1 2) sourceC1110) = raw18654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18654; decide +kernel
    rw [ha]
    exact (canonical18654 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1110 + difference 2 3) (sourceB1110 + difference 3 2) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1110 + difference 2 3) (sourceB1110 + difference 3 2) sourceC1110) = raw3040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw3040; decide +kernel
    rw [ha]
    exact (canonical3040 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1110 + difference 2 4) (sourceB1110 + difference 4 2) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1110 + difference 2 4) (sourceB1110 + difference 4 2) sourceC1110) = raw18655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18655; decide +kernel
    rw [ha]
    exact (canonical18655 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1110 + difference 2 5) (sourceB1110 + difference 5 2) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1110 + difference 2 5) (sourceB1110 + difference 5 2) sourceC1110) = raw18656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18656; decide +kernel
    rw [ha]
    exact (canonical18656 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1110 + difference 3 0) (sourceB1110 + difference 0 3) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA1110 + difference 3 0) (sourceB1110 + difference 0 3) sourceC1110) = raw13583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw13583; decide +kernel
    rw [ha]
    exact (canonical13583 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1110 + difference 3 1) (sourceB1110 + difference 1 3) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA1110 + difference 3 1) (sourceB1110 + difference 1 3) sourceC1110) = raw18657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18657; decide +kernel
    rw [ha]
    exact (canonical18657 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1110 + difference 3 2) (sourceB1110 + difference 2 3) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1110 + difference 3 2) (sourceB1110 + difference 2 3) sourceC1110) = raw18658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18658; decide +kernel
    rw [ha]
    exact (canonical18658 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1110 + difference 3 4) (sourceB1110 + difference 4 3) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1110 + difference 3 4) (sourceB1110 + difference 4 3) sourceC1110) = raw18659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18659; decide +kernel
    rw [ha]
    exact (canonical18659 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1110 + difference 3 5) (sourceB1110 + difference 5 3) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1110 + difference 3 5) (sourceB1110 + difference 5 3) sourceC1110) = raw18660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18660; decide +kernel
    rw [ha]
    exact (canonical18660 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1110 + difference 4 0) (sourceB1110 + difference 0 4) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA1110 + difference 4 0) (sourceB1110 + difference 0 4) sourceC1110) = raw13588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw13588; decide +kernel
    rw [ha]
    exact (canonical13588 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1110 + difference 4 1) (sourceB1110 + difference 1 4) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA1110 + difference 4 1) (sourceB1110 + difference 1 4) sourceC1110) = raw18661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18661; decide +kernel
    rw [ha]
    exact (canonical18661 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1110 + difference 4 2) (sourceB1110 + difference 2 4) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1110 + difference 4 2) (sourceB1110 + difference 2 4) sourceC1110) = raw18662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18662; decide +kernel
    rw [ha]
    exact (canonical18662 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1110 + difference 4 3) (sourceB1110 + difference 3 4) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1110 + difference 4 3) (sourceB1110 + difference 3 4) sourceC1110) = raw3050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw3050; decide +kernel
    rw [ha]
    exact (canonical3050 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1110 + difference 4 5) (sourceB1110 + difference 5 4) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1110 + difference 4 5) (sourceB1110 + difference 5 4) sourceC1110) = raw18663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw18663; decide +kernel
    rw [ha]
    exact (canonical18663 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1110 + difference 5 0) (sourceB1110 + difference 0 5) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1110 + difference 5 0) (sourceB1110 + difference 0 5) sourceC1110) = raw13592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw13592; decide +kernel
    rw [ha]
    exact (canonical13592 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1110 + difference 5 1) (sourceB1110 + difference 1 5) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA1110 + difference 5 1) (sourceB1110 + difference 1 5) sourceC1110) = raw17691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw17691; decide +kernel
    rw [ha]
    exact (canonical17691 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1110 + difference 5 2) (sourceB1110 + difference 2 5) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1110 + difference 5 2) (sourceB1110 + difference 2 5) sourceC1110) = raw17692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw17692; decide +kernel
    rw [ha]
    exact (canonical17692 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1110 + difference 5 3) (sourceB1110 + difference 3 5) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1110 + difference 5 3) (sourceB1110 + difference 3 5) sourceC1110) = raw3055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw3055; decide +kernel
    rw [ha]
    exact (canonical3055 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1110 + difference 5 4) (sourceB1110 + difference 4 5) sourceC1110) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1110 + difference 5 4) (sourceB1110 + difference 4 5) sourceC1110) = raw17693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1110 sourceB1110 sourceC1110 difference raw17693; decide +kernel
    rw [ha]
    exact (canonical17693 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1110 sourceB1110 sourceC1110
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1110, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1111 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1111 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1111 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceForm1111 : Integer.Sparse Master := [(Sum.inr 5098, 1), (Sum.inr 5099, 1), (Sum.inr 5102, 2), (Sum.inr 5247, 1), (Sum.inr 5248, 1), (Sum.inr 5271, 2), (Sum.inr 5306, 1), (Sum.inr 5365, 1), (Sum.inr 5368, 2), (Sum.inr 5439, 1), (Sum.inr 5469, 2), (Sum.inr 5473, 2), (Sum.inr 5478, 2), (Sum.inr 5482, 1), (Sum.inr 5483, 2), (Sum.inr 5485, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2), (Sum.inr 5492, 2), (Sum.inr 5493, 1), (Sum.inr 5499, 1)]

theorem sourceEq1111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1111 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1111 + difference 0 1) (sourceB1111 + difference 1 0) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1111 + difference 0 1) (sourceB1111 + difference 1 0) sourceC1111) = raw18664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18664; decide +kernel
    rw [ha]
    exact (canonical18664 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1111 + difference 0 2) (sourceB1111 + difference 2 0) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1111 + difference 0 2) (sourceB1111 + difference 2 0) sourceC1111) = raw18665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18665; decide +kernel
    rw [ha]
    exact (canonical18665 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1111 + difference 0 3) (sourceB1111 + difference 3 0) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1111 + difference 0 3) (sourceB1111 + difference 3 0) sourceC1111) = raw18666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18666; decide +kernel
    rw [ha]
    exact (canonical18666 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1111 + difference 0 4) (sourceB1111 + difference 4 0) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1111 + difference 0 4) (sourceB1111 + difference 4 0) sourceC1111) = raw18667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18667; decide +kernel
    rw [ha]
    exact (canonical18667 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1111 + difference 0 5) (sourceB1111 + difference 5 0) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA1111 + difference 0 5) (sourceB1111 + difference 5 0) sourceC1111) = raw18668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18668; decide +kernel
    rw [ha]
    exact (canonical18668 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1111 + difference 1 0) (sourceB1111 + difference 0 1) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA1111 + difference 1 0) (sourceB1111 + difference 0 1) sourceC1111) = raw10691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw10691; decide +kernel
    rw [ha]
    exact (canonical10691 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1111 + difference 1 2) (sourceB1111 + difference 2 1) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1111 + difference 1 2) (sourceB1111 + difference 2 1) sourceC1111) = raw12132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw12132; decide +kernel
    rw [ha]
    exact (canonical12132 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1111 + difference 1 3) (sourceB1111 + difference 3 1) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1111 + difference 1 3) (sourceB1111 + difference 3 1) sourceC1111) = raw10676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw10676; decide +kernel
    rw [ha]
    exact (canonical10676 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1111 + difference 1 4) (sourceB1111 + difference 4 1) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1111 + difference 1 4) (sourceB1111 + difference 4 1) sourceC1111) = raw12133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw12133; decide +kernel
    rw [ha]
    exact (canonical12133 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1111 + difference 1 5) (sourceB1111 + difference 5 1) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1111 + difference 1 5) (sourceB1111 + difference 5 1) sourceC1111) = raw12134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw12134; decide +kernel
    rw [ha]
    exact (canonical12134 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1111 + difference 2 0) (sourceB1111 + difference 0 2) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA1111 + difference 2 0) (sourceB1111 + difference 0 2) sourceC1111) = raw12140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw12140; decide +kernel
    rw [ha]
    exact (canonical12140 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1111 + difference 2 1) (sourceB1111 + difference 1 2) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1111 + difference 2 1) (sourceB1111 + difference 1 2) sourceC1111) = raw18669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18669; decide +kernel
    rw [ha]
    exact (canonical18669 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1111 + difference 2 3) (sourceB1111 + difference 3 2) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1111 + difference 2 3) (sourceB1111 + difference 3 2) sourceC1111) = raw18670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18670; decide +kernel
    rw [ha]
    exact (canonical18670 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1111 + difference 2 4) (sourceB1111 + difference 4 2) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1111 + difference 2 4) (sourceB1111 + difference 4 2) sourceC1111) = raw18671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18671; decide +kernel
    rw [ha]
    exact (canonical18671 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1111 + difference 2 5) (sourceB1111 + difference 5 2) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1111 + difference 2 5) (sourceB1111 + difference 5 2) sourceC1111) = raw18672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18672; decide +kernel
    rw [ha]
    exact (canonical18672 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1111 + difference 3 0) (sourceB1111 + difference 0 3) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1111 + difference 3 0) (sourceB1111 + difference 0 3) sourceC1111) = raw12144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw12144; decide +kernel
    rw [ha]
    exact (canonical12144 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1111 + difference 3 1) (sourceB1111 + difference 1 3) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1111 + difference 3 1) (sourceB1111 + difference 1 3) sourceC1111) = raw18673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18673; decide +kernel
    rw [ha]
    exact (canonical18673 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1111 + difference 3 2) (sourceB1111 + difference 2 3) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1111 + difference 3 2) (sourceB1111 + difference 2 3) sourceC1111) = raw18674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18674; decide +kernel
    rw [ha]
    exact (canonical18674 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1111 + difference 3 4) (sourceB1111 + difference 4 3) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1111 + difference 3 4) (sourceB1111 + difference 4 3) sourceC1111) = raw18675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18675; decide +kernel
    rw [ha]
    exact (canonical18675 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1111 + difference 3 5) (sourceB1111 + difference 5 3) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1111 + difference 3 5) (sourceB1111 + difference 5 3) sourceC1111) = raw18676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18676; decide +kernel
    rw [ha]
    exact (canonical18676 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1111 + difference 4 0) (sourceB1111 + difference 0 4) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1111 + difference 4 0) (sourceB1111 + difference 0 4) sourceC1111) = raw12149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw12149; decide +kernel
    rw [ha]
    exact (canonical12149 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1111 + difference 4 1) (sourceB1111 + difference 1 4) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1111 + difference 4 1) (sourceB1111 + difference 1 4) sourceC1111) = raw18677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18677; decide +kernel
    rw [ha]
    exact (canonical18677 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1111 + difference 4 2) (sourceB1111 + difference 2 4) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1111 + difference 4 2) (sourceB1111 + difference 2 4) sourceC1111) = raw18678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18678; decide +kernel
    rw [ha]
    exact (canonical18678 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1111 + difference 4 3) (sourceB1111 + difference 3 4) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1111 + difference 4 3) (sourceB1111 + difference 3 4) sourceC1111) = raw18679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18679; decide +kernel
    rw [ha]
    exact (canonical18679 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1111 + difference 4 5) (sourceB1111 + difference 5 4) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1111 + difference 4 5) (sourceB1111 + difference 5 4) sourceC1111) = raw18680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18680; decide +kernel
    rw [ha]
    exact (canonical18680 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1111 + difference 5 0) (sourceB1111 + difference 0 5) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA1111 + difference 5 0) (sourceB1111 + difference 0 5) sourceC1111) = raw10688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw10688; decide +kernel
    rw [ha]
    exact (canonical10688 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1111 + difference 5 1) (sourceB1111 + difference 1 5) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA1111 + difference 5 1) (sourceB1111 + difference 1 5) sourceC1111) = raw18681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18681; decide +kernel
    rw [ha]
    exact (canonical18681 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1111 + difference 5 2) (sourceB1111 + difference 2 5) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA1111 + difference 5 2) (sourceB1111 + difference 2 5) sourceC1111) = raw18682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18682; decide +kernel
    rw [ha]
    exact (canonical18682 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1111 + difference 5 3) (sourceB1111 + difference 3 5) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1111 + difference 5 3) (sourceB1111 + difference 3 5) sourceC1111) = raw10672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw10672; decide +kernel
    rw [ha]
    exact (canonical10672 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1111 + difference 5 4) (sourceB1111 + difference 4 5) sourceC1111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1111 + difference 5 4) (sourceB1111 + difference 4 5) sourceC1111) = raw18683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1111 sourceB1111 sourceC1111 difference raw18683; decide +kernel
    rw [ha]
    exact (canonical18683 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1111 sourceB1111 sourceC1111
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1111, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1112 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1112 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC1112 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceForm1112 : Integer.Sparse Master := [(Sum.inr 5069, 1), (Sum.inr 5071, 1), (Sum.inr 5074, 1), (Sum.inr 5092, 1), (Sum.inr 5132, 1), (Sum.inr 5138, 1), (Sum.inr 5160, 1), (Sum.inr 5255, 1), (Sum.inr 5289, 1), (Sum.inr 5350, 1), (Sum.inr 5353, 1), (Sum.inr 5362, 1), (Sum.inr 5401, 1), (Sum.inr 5405, 1), (Sum.inr 5419, 1), (Sum.inr 5421, 1), (Sum.inr 5424, 1), (Sum.inr 5430, 2), (Sum.inr 5438, 1), (Sum.inr 5461, 1), (Sum.inr 5470, 1), (Sum.inr 5471, 1), (Sum.inr 5478, 1), (Sum.inr 5480, 1), (Sum.inr 5481, 1), (Sum.inr 5482, 1), (Sum.inr 5484, 2), (Sum.inr 5485, 1)]

theorem sourceEq1112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1112 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1112 + difference 0 1) (sourceB1112 + difference 1 0) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1112 + difference 0 1) (sourceB1112 + difference 1 0) sourceC1112) = raw18684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18684; decide +kernel
    rw [ha]
    exact (canonical18684 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1112 + difference 0 2) (sourceB1112 + difference 2 0) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1112 + difference 0 2) (sourceB1112 + difference 2 0) sourceC1112) = raw18685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18685; decide +kernel
    rw [ha]
    exact (canonical18685 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1112 + difference 0 3) (sourceB1112 + difference 3 0) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1112 + difference 0 3) (sourceB1112 + difference 3 0) sourceC1112) = raw17525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw17525; decide +kernel
    rw [ha]
    exact (canonical17525 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1112 + difference 0 4) (sourceB1112 + difference 4 0) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1112 + difference 0 4) (sourceB1112 + difference 4 0) sourceC1112) = raw18686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18686; decide +kernel
    rw [ha]
    exact (canonical18686 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1112 + difference 0 5) (sourceB1112 + difference 5 0) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1112 + difference 0 5) (sourceB1112 + difference 5 0) sourceC1112) = raw18687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18687; decide +kernel
    rw [ha]
    exact (canonical18687 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1112 + difference 1 0) (sourceB1112 + difference 0 1) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA1112 + difference 1 0) (sourceB1112 + difference 0 1) sourceC1112) = raw18688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18688; decide +kernel
    rw [ha]
    exact (canonical18688 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1112 + difference 1 2) (sourceB1112 + difference 2 1) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1112 + difference 1 2) (sourceB1112 + difference 2 1) sourceC1112) = raw18689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18689; decide +kernel
    rw [ha]
    exact (canonical18689 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1112 + difference 1 3) (sourceB1112 + difference 3 1) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1112 + difference 1 3) (sourceB1112 + difference 3 1) sourceC1112) = raw17530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw17530; decide +kernel
    rw [ha]
    exact (canonical17530 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1112 + difference 1 4) (sourceB1112 + difference 4 1) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1112 + difference 1 4) (sourceB1112 + difference 4 1) sourceC1112) = raw18690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18690; decide +kernel
    rw [ha]
    exact (canonical18690 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1112 + difference 1 5) (sourceB1112 + difference 5 1) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1112 + difference 1 5) (sourceB1112 + difference 5 1) sourceC1112) = raw18691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18691; decide +kernel
    rw [ha]
    exact (canonical18691 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1112 + difference 2 0) (sourceB1112 + difference 0 2) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA1112 + difference 2 0) (sourceB1112 + difference 0 2) sourceC1112) = raw18692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18692; decide +kernel
    rw [ha]
    exact (canonical18692 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1112 + difference 2 1) (sourceB1112 + difference 1 2) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5461) := by
    have ha : (tripleCharges (sourceA1112 + difference 2 1) (sourceB1112 + difference 1 2) sourceC1112) = raw18693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18693; decide +kernel
    rw [ha]
    exact (canonical18693 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1112 + difference 2 3) (sourceB1112 + difference 3 2) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1112 + difference 2 3) (sourceB1112 + difference 3 2) sourceC1112) = raw17535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw17535; decide +kernel
    rw [ha]
    exact (canonical17535 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1112 + difference 2 4) (sourceB1112 + difference 4 2) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1112 + difference 2 4) (sourceB1112 + difference 4 2) sourceC1112) = raw18694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18694; decide +kernel
    rw [ha]
    exact (canonical18694 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1112 + difference 2 5) (sourceB1112 + difference 5 2) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1112 + difference 2 5) (sourceB1112 + difference 5 2) sourceC1112) = raw18695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18695; decide +kernel
    rw [ha]
    exact (canonical18695 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1112 + difference 3 0) (sourceB1112 + difference 0 3) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5069) := by
    have ha : (tripleCharges (sourceA1112 + difference 3 0) (sourceB1112 + difference 0 3) sourceC1112) = raw18696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18696; decide +kernel
    rw [ha]
    exact (canonical18696 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1112 + difference 3 1) (sourceB1112 + difference 1 3) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5092) := by
    have ha : (tripleCharges (sourceA1112 + difference 3 1) (sourceB1112 + difference 1 3) sourceC1112) = raw18697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18697; decide +kernel
    rw [ha]
    exact (canonical18697 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1112 + difference 3 2) (sourceB1112 + difference 2 3) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA1112 + difference 3 2) (sourceB1112 + difference 2 3) sourceC1112) = raw18698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18698; decide +kernel
    rw [ha]
    exact (canonical18698 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1112 + difference 3 4) (sourceB1112 + difference 4 3) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA1112 + difference 3 4) (sourceB1112 + difference 4 3) sourceC1112) = raw18699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18699; decide +kernel
    rw [ha]
    exact (canonical18699 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1112 + difference 3 5) (sourceB1112 + difference 5 3) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA1112 + difference 3 5) (sourceB1112 + difference 5 3) sourceC1112) = raw18700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18700; decide +kernel
    rw [ha]
    exact (canonical18700 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1112 + difference 4 0) (sourceB1112 + difference 0 4) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5132) := by
    have ha : (tripleCharges (sourceA1112 + difference 4 0) (sourceB1112 + difference 0 4) sourceC1112) = raw18701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18701; decide +kernel
    rw [ha]
    exact (canonical18701 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1112 + difference 4 1) (sourceB1112 + difference 1 4) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5362) := by
    have ha : (tripleCharges (sourceA1112 + difference 4 1) (sourceB1112 + difference 1 4) sourceC1112) = raw18702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18702; decide +kernel
    rw [ha]
    exact (canonical18702 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1112 + difference 4 2) (sourceB1112 + difference 2 4) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA1112 + difference 4 2) (sourceB1112 + difference 2 4) sourceC1112) = raw18703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18703; decide +kernel
    rw [ha]
    exact (canonical18703 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1112 + difference 4 3) (sourceB1112 + difference 3 4) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1112 + difference 4 3) (sourceB1112 + difference 3 4) sourceC1112) = raw17545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw17545; decide +kernel
    rw [ha]
    exact (canonical17545 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1112 + difference 4 5) (sourceB1112 + difference 5 4) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1112 + difference 4 5) (sourceB1112 + difference 5 4) sourceC1112) = raw18704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18704; decide +kernel
    rw [ha]
    exact (canonical18704 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1112 + difference 5 0) (sourceB1112 + difference 0 5) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA1112 + difference 5 0) (sourceB1112 + difference 0 5) sourceC1112) = raw17536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw17536; decide +kernel
    rw [ha]
    exact (canonical17536 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1112 + difference 5 1) (sourceB1112 + difference 1 5) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5419) := by
    have ha : (tripleCharges (sourceA1112 + difference 5 1) (sourceB1112 + difference 1 5) sourceC1112) = raw17537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw17537; decide +kernel
    rw [ha]
    exact (canonical17537 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1112 + difference 5 2) (sourceB1112 + difference 2 5) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1112 + difference 5 2) (sourceB1112 + difference 2 5) sourceC1112) = raw17538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw17538; decide +kernel
    rw [ha]
    exact (canonical17538 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1112 + difference 5 3) (sourceB1112 + difference 3 5) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1112 + difference 5 3) (sourceB1112 + difference 3 5) sourceC1112) = raw18705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw18705; decide +kernel
    rw [ha]
    exact (canonical18705 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1112 + difference 5 4) (sourceB1112 + difference 4 5) sourceC1112) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1112 + difference 5 4) (sourceB1112 + difference 4 5) sourceC1112) = raw17539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1112 sourceB1112 sourceC1112 difference raw17539; decide +kernel
    rw [ha]
    exact (canonical17539 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1112 sourceB1112 sourceC1112
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1112, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1113 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1113 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC1113 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceForm1113 : Integer.Sparse Master := [(Sum.inr 2550, 1), (Sum.inr 2551, 1), (Sum.inr 2557, 1), (Sum.inr 2587, 1), (Sum.inr 2718, 1), (Sum.inr 3442, 1), (Sum.inr 3445, 1), (Sum.inr 3463, 1), (Sum.inr 3572, 1), (Sum.inr 3748, 1), (Sum.inr 3750, 1), (Sum.inr 3761, 1), (Sum.inr 3804, 1), (Sum.inr 3805, 1), (Sum.inr 3848, 1), (Sum.inr 3871, 1), (Sum.inr 3922, 1), (Sum.inr 3927, 1), (Sum.inr 3946, 1), (Sum.inr 3955, 1), (Sum.inr 3956, 1), (Sum.inr 3978, 1), (Sum.inr 3979, 1), (Sum.inr 3980, 1), (Sum.inr 3983, 1), (Sum.inr 3984, 1), (Sum.inr 3990, 1), (Sum.inr 3993, 1), (Sum.inr 3994, 1), (Sum.inr 3997, 1)]

theorem sourceEq1113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1113 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1113 + difference 0 1) (sourceB1113 + difference 1 0) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1113 + difference 0 1) (sourceB1113 + difference 1 0) sourceC1113) = raw18706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18706; decide +kernel
    rw [ha]
    exact (canonical18706 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1113 + difference 0 2) (sourceB1113 + difference 2 0) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA1113 + difference 0 2) (sourceB1113 + difference 2 0) sourceC1113) = raw18707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18707; decide +kernel
    rw [ha]
    exact (canonical18707 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1113 + difference 0 3) (sourceB1113 + difference 3 0) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA1113 + difference 0 3) (sourceB1113 + difference 3 0) sourceC1113) = raw18708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18708; decide +kernel
    rw [ha]
    exact (canonical18708 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1113 + difference 0 4) (sourceB1113 + difference 4 0) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA1113 + difference 0 4) (sourceB1113 + difference 4 0) sourceC1113) = raw18709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18709; decide +kernel
    rw [ha]
    exact (canonical18709 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1113 + difference 0 5) (sourceB1113 + difference 5 0) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA1113 + difference 0 5) (sourceB1113 + difference 5 0) sourceC1113) = raw18710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18710; decide +kernel
    rw [ha]
    exact (canonical18710 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1113 + difference 1 0) (sourceB1113 + difference 0 1) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA1113 + difference 1 0) (sourceB1113 + difference 0 1) sourceC1113) = raw18711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18711; decide +kernel
    rw [ha]
    exact (canonical18711 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1113 + difference 1 2) (sourceB1113 + difference 2 1) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA1113 + difference 1 2) (sourceB1113 + difference 2 1) sourceC1113) = raw18712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18712; decide +kernel
    rw [ha]
    exact (canonical18712 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1113 + difference 1 3) (sourceB1113 + difference 3 1) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA1113 + difference 1 3) (sourceB1113 + difference 3 1) sourceC1113) = raw18713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18713; decide +kernel
    rw [ha]
    exact (canonical18713 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1113 + difference 1 4) (sourceB1113 + difference 4 1) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1113 + difference 1 4) (sourceB1113 + difference 4 1) sourceC1113) = raw18714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18714; decide +kernel
    rw [ha]
    exact (canonical18714 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1113 + difference 1 5) (sourceB1113 + difference 5 1) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1113 + difference 1 5) (sourceB1113 + difference 5 1) sourceC1113) = raw18715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18715; decide +kernel
    rw [ha]
    exact (canonical18715 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1113 + difference 2 0) (sourceB1113 + difference 0 2) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA1113 + difference 2 0) (sourceB1113 + difference 0 2) sourceC1113) = raw18716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18716; decide +kernel
    rw [ha]
    exact (canonical18716 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1113 + difference 2 1) (sourceB1113 + difference 1 2) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3927) := by
    have ha : (tripleCharges (sourceA1113 + difference 2 1) (sourceB1113 + difference 1 2) sourceC1113) = raw18717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18717; decide +kernel
    rw [ha]
    exact (canonical18717 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1113 + difference 2 3) (sourceB1113 + difference 3 2) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA1113 + difference 2 3) (sourceB1113 + difference 3 2) sourceC1113) = raw18718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18718; decide +kernel
    rw [ha]
    exact (canonical18718 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1113 + difference 2 4) (sourceB1113 + difference 4 2) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3997) := by
    have ha : (tripleCharges (sourceA1113 + difference 2 4) (sourceB1113 + difference 4 2) sourceC1113) = raw18719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18719; decide +kernel
    rw [ha]
    exact (canonical18719 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1113 + difference 2 5) (sourceB1113 + difference 5 2) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1113 + difference 2 5) (sourceB1113 + difference 5 2) sourceC1113) = raw18720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18720; decide +kernel
    rw [ha]
    exact (canonical18720 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1113 + difference 3 0) (sourceB1113 + difference 0 3) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2550) := by
    have ha : (tripleCharges (sourceA1113 + difference 3 0) (sourceB1113 + difference 0 3) sourceC1113) = raw18721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18721; decide +kernel
    rw [ha]
    exact (canonical18721 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1113 + difference 3 1) (sourceB1113 + difference 1 3) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3442) := by
    have ha : (tripleCharges (sourceA1113 + difference 3 1) (sourceB1113 + difference 1 3) sourceC1113) = raw18722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18722; decide +kernel
    rw [ha]
    exact (canonical18722 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1113 + difference 3 2) (sourceB1113 + difference 2 3) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3445) := by
    have ha : (tripleCharges (sourceA1113 + difference 3 2) (sourceB1113 + difference 2 3) sourceC1113) = raw18723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18723; decide +kernel
    rw [ha]
    exact (canonical18723 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1113 + difference 3 4) (sourceB1113 + difference 4 3) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA1113 + difference 3 4) (sourceB1113 + difference 4 3) sourceC1113) = raw18724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18724; decide +kernel
    rw [ha]
    exact (canonical18724 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1113 + difference 3 5) (sourceB1113 + difference 5 3) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA1113 + difference 3 5) (sourceB1113 + difference 5 3) sourceC1113) = raw18725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18725; decide +kernel
    rw [ha]
    exact (canonical18725 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1113 + difference 4 0) (sourceB1113 + difference 0 4) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2551) := by
    have ha : (tripleCharges (sourceA1113 + difference 4 0) (sourceB1113 + difference 0 4) sourceC1113) = raw18726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18726; decide +kernel
    rw [ha]
    exact (canonical18726 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1113 + difference 4 1) (sourceB1113 + difference 1 4) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3748) := by
    have ha : (tripleCharges (sourceA1113 + difference 4 1) (sourceB1113 + difference 1 4) sourceC1113) = raw18727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18727; decide +kernel
    rw [ha]
    exact (canonical18727 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1113 + difference 4 2) (sourceB1113 + difference 2 4) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3750) := by
    have ha : (tripleCharges (sourceA1113 + difference 4 2) (sourceB1113 + difference 2 4) sourceC1113) = raw18728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18728; decide +kernel
    rw [ha]
    exact (canonical18728 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1113 + difference 4 3) (sourceB1113 + difference 3 4) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1113 + difference 4 3) (sourceB1113 + difference 3 4) sourceC1113) = raw18729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18729; decide +kernel
    rw [ha]
    exact (canonical18729 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1113 + difference 4 5) (sourceB1113 + difference 5 4) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA1113 + difference 4 5) (sourceB1113 + difference 5 4) sourceC1113) = raw18730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18730; decide +kernel
    rw [ha]
    exact (canonical18730 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1113 + difference 5 0) (sourceB1113 + difference 0 5) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA1113 + difference 5 0) (sourceB1113 + difference 0 5) sourceC1113) = raw18731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18731; decide +kernel
    rw [ha]
    exact (canonical18731 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1113 + difference 5 1) (sourceB1113 + difference 1 5) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3922) := by
    have ha : (tripleCharges (sourceA1113 + difference 5 1) (sourceB1113 + difference 1 5) sourceC1113) = raw18732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18732; decide +kernel
    rw [ha]
    exact (canonical18732 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1113 + difference 5 2) (sourceB1113 + difference 2 5) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA1113 + difference 5 2) (sourceB1113 + difference 2 5) sourceC1113) = raw18733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18733; decide +kernel
    rw [ha]
    exact (canonical18733 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1113 + difference 5 3) (sourceB1113 + difference 3 5) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA1113 + difference 5 3) (sourceB1113 + difference 3 5) sourceC1113) = raw18734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18734; decide +kernel
    rw [ha]
    exact (canonical18734 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1113 + difference 5 4) (sourceB1113 + difference 4 5) sourceC1113) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA1113 + difference 5 4) (sourceB1113 + difference 4 5) sourceC1113) = raw18735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1113 sourceB1113 sourceC1113 difference raw18735; decide +kernel
    rw [ha]
    exact (canonical18735 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1113 sourceB1113 sourceC1113
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1113, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1114 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1114 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC1114 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceForm1114 : Integer.Sparse Master := [(Sum.inr 2476, 1), (Sum.inr 2478, 1), (Sum.inr 2481, 1), (Sum.inr 2501, 1), (Sum.inr 2763, 1), (Sum.inr 3499, 1), (Sum.inr 3503, 1), (Sum.inr 3517, 1), (Sum.inr 3558, 1), (Sum.inr 3688, 1), (Sum.inr 3691, 1), (Sum.inr 3700, 1), (Sum.inr 3842, 1), (Sum.inr 3843, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 3873, 1), (Sum.inr 3947, 1), (Sum.inr 3966, 1), (Sum.inr 3972, 1), (Sum.inr 3973, 1), (Sum.inr 3974, 1), (Sum.inr 3976, 1), (Sum.inr 3977, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 3991, 1), (Sum.inr 3992, 1), (Sum.inr 3997, 1), (Sum.inr 3998, 1)]

theorem sourceEq1114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1114 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1114 + difference 0 1) (sourceB1114 + difference 1 0) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1114 + difference 0 1) (sourceB1114 + difference 1 0) sourceC1114) = raw18736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18736; decide +kernel
    rw [ha]
    exact (canonical18736 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1114 + difference 0 2) (sourceB1114 + difference 2 0) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3976) := by
    have ha : (tripleCharges (sourceA1114 + difference 0 2) (sourceB1114 + difference 2 0) sourceC1114) = raw18737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18737; decide +kernel
    rw [ha]
    exact (canonical18737 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1114 + difference 0 3) (sourceB1114 + difference 3 0) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA1114 + difference 0 3) (sourceB1114 + difference 3 0) sourceC1114) = raw17555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw17555; decide +kernel
    rw [ha]
    exact (canonical17555 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1114 + difference 0 4) (sourceB1114 + difference 4 0) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA1114 + difference 0 4) (sourceB1114 + difference 4 0) sourceC1114) = raw18738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18738; decide +kernel
    rw [ha]
    exact (canonical18738 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1114 + difference 0 5) (sourceB1114 + difference 5 0) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA1114 + difference 0 5) (sourceB1114 + difference 5 0) sourceC1114) = raw18739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18739; decide +kernel
    rw [ha]
    exact (canonical18739 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1114 + difference 1 0) (sourceB1114 + difference 0 1) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA1114 + difference 1 0) (sourceB1114 + difference 0 1) sourceC1114) = raw18740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18740; decide +kernel
    rw [ha]
    exact (canonical18740 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1114 + difference 1 2) (sourceB1114 + difference 2 1) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA1114 + difference 1 2) (sourceB1114 + difference 2 1) sourceC1114) = raw18741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18741; decide +kernel
    rw [ha]
    exact (canonical18741 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1114 + difference 1 3) (sourceB1114 + difference 3 1) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3991) := by
    have ha : (tripleCharges (sourceA1114 + difference 1 3) (sourceB1114 + difference 3 1) sourceC1114) = raw17560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw17560; decide +kernel
    rw [ha]
    exact (canonical17560 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1114 + difference 1 4) (sourceB1114 + difference 4 1) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3997) := by
    have ha : (tripleCharges (sourceA1114 + difference 1 4) (sourceB1114 + difference 4 1) sourceC1114) = raw18742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18742; decide +kernel
    rw [ha]
    exact (canonical18742 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1114 + difference 1 5) (sourceB1114 + difference 5 1) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3966) := by
    have ha : (tripleCharges (sourceA1114 + difference 1 5) (sourceB1114 + difference 5 1) sourceC1114) = raw18743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18743; decide +kernel
    rw [ha]
    exact (canonical18743 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1114 + difference 2 0) (sourceB1114 + difference 0 2) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA1114 + difference 2 0) (sourceB1114 + difference 0 2) sourceC1114) = raw18744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18744; decide +kernel
    rw [ha]
    exact (canonical18744 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1114 + difference 2 1) (sourceB1114 + difference 1 2) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3973) := by
    have ha : (tripleCharges (sourceA1114 + difference 2 1) (sourceB1114 + difference 1 2) sourceC1114) = raw18745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18745; decide +kernel
    rw [ha]
    exact (canonical18745 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1114 + difference 2 3) (sourceB1114 + difference 3 2) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA1114 + difference 2 3) (sourceB1114 + difference 3 2) sourceC1114) = raw17565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw17565; decide +kernel
    rw [ha]
    exact (canonical17565 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1114 + difference 2 4) (sourceB1114 + difference 4 2) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1114 + difference 2 4) (sourceB1114 + difference 4 2) sourceC1114) = raw18746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18746; decide +kernel
    rw [ha]
    exact (canonical18746 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1114 + difference 2 5) (sourceB1114 + difference 5 2) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA1114 + difference 2 5) (sourceB1114 + difference 5 2) sourceC1114) = raw18747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18747; decide +kernel
    rw [ha]
    exact (canonical18747 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1114 + difference 3 0) (sourceB1114 + difference 0 3) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2476) := by
    have ha : (tripleCharges (sourceA1114 + difference 3 0) (sourceB1114 + difference 0 3) sourceC1114) = raw18748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18748; decide +kernel
    rw [ha]
    exact (canonical18748 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1114 + difference 3 1) (sourceB1114 + difference 1 3) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2501) := by
    have ha : (tripleCharges (sourceA1114 + difference 3 1) (sourceB1114 + difference 1 3) sourceC1114) = raw18749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18749; decide +kernel
    rw [ha]
    exact (canonical18749 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1114 + difference 3 2) (sourceB1114 + difference 2 3) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2478) := by
    have ha : (tripleCharges (sourceA1114 + difference 3 2) (sourceB1114 + difference 2 3) sourceC1114) = raw18750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18750; decide +kernel
    rw [ha]
    exact (canonical18750 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1114 + difference 3 4) (sourceB1114 + difference 4 3) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA1114 + difference 3 4) (sourceB1114 + difference 4 3) sourceC1114) = raw18751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18751; decide +kernel
    rw [ha]
    exact (canonical18751 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1114 + difference 3 5) (sourceB1114 + difference 5 3) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA1114 + difference 3 5) (sourceB1114 + difference 5 3) sourceC1114) = raw18752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18752; decide +kernel
    rw [ha]
    exact (canonical18752 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1114 + difference 4 0) (sourceB1114 + difference 0 4) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3499) := by
    have ha : (tripleCharges (sourceA1114 + difference 4 0) (sourceB1114 + difference 0 4) sourceC1114) = raw18753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18753; decide +kernel
    rw [ha]
    exact (canonical18753 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1114 + difference 4 1) (sourceB1114 + difference 1 4) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3700) := by
    have ha : (tripleCharges (sourceA1114 + difference 4 1) (sourceB1114 + difference 1 4) sourceC1114) = raw18754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18754; decide +kernel
    rw [ha]
    exact (canonical18754 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1114 + difference 4 2) (sourceB1114 + difference 2 4) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3688) := by
    have ha : (tripleCharges (sourceA1114 + difference 4 2) (sourceB1114 + difference 2 4) sourceC1114) = raw18755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18755; decide +kernel
    rw [ha]
    exact (canonical18755 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1114 + difference 4 3) (sourceB1114 + difference 3 4) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1114 + difference 4 3) (sourceB1114 + difference 3 4) sourceC1114) = raw17575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw17575; decide +kernel
    rw [ha]
    exact (canonical17575 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1114 + difference 4 5) (sourceB1114 + difference 5 4) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA1114 + difference 4 5) (sourceB1114 + difference 5 4) sourceC1114) = raw18756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18756; decide +kernel
    rw [ha]
    exact (canonical18756 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1114 + difference 5 0) (sourceB1114 + difference 0 5) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA1114 + difference 5 0) (sourceB1114 + difference 0 5) sourceC1114) = raw17566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw17566; decide +kernel
    rw [ha]
    exact (canonical17566 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1114 + difference 5 1) (sourceB1114 + difference 1 5) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3842) := by
    have ha : (tripleCharges (sourceA1114 + difference 5 1) (sourceB1114 + difference 1 5) sourceC1114) = raw17567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw17567; decide +kernel
    rw [ha]
    exact (canonical17567 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1114 + difference 5 2) (sourceB1114 + difference 2 5) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1114 + difference 5 2) (sourceB1114 + difference 2 5) sourceC1114) = raw17568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw17568; decide +kernel
    rw [ha]
    exact (canonical17568 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1114 + difference 5 3) (sourceB1114 + difference 3 5) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA1114 + difference 5 3) (sourceB1114 + difference 3 5) sourceC1114) = raw18757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw18757; decide +kernel
    rw [ha]
    exact (canonical18757 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1114 + difference 5 4) (sourceB1114 + difference 4 5) sourceC1114) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1114 + difference 5 4) (sourceB1114 + difference 4 5) sourceC1114) = raw17569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1114 sourceB1114 sourceC1114 difference raw17569; decide +kernel
    rw [ha]
    exact (canonical17569 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1114 sourceB1114 sourceC1114
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1114, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1115 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1115 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC1115 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceForm1115 : Integer.Sparse Master := [(Sum.inr 2933, 1), (Sum.inr 2935, 1), (Sum.inr 2938, 1), (Sum.inr 2951, 1), (Sum.inr 3084, 1), (Sum.inr 3978, 1), (Sum.inr 4091, -1)]

theorem sourceEq1115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1115 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1115 + difference 0 0) (sourceB1115 + difference 0 0) sourceC1115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1115 + difference 0 0) (sourceB1115 + difference 0 0) sourceC1115) = raw18758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1115 sourceB1115 sourceC1115 difference raw18758; decide +kernel
    rw [ha]
    exact (canonical18758 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1115 + difference 1 0) (sourceB1115 + difference 0 1) sourceC1115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA1115 + difference 1 0) (sourceB1115 + difference 0 1) sourceC1115) = raw18759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1115 sourceB1115 sourceC1115 difference raw18759; decide +kernel
    rw [ha]
    exact (canonical18759 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1115 + difference 2 0) (sourceB1115 + difference 0 2) sourceC1115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA1115 + difference 2 0) (sourceB1115 + difference 0 2) sourceC1115) = raw18760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1115 sourceB1115 sourceC1115 difference raw18760; decide +kernel
    rw [ha]
    exact (canonical18760 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1115 + difference 3 0) (sourceB1115 + difference 0 3) sourceC1115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2938) := by
    have ha : (tripleCharges (sourceA1115 + difference 3 0) (sourceB1115 + difference 0 3) sourceC1115) = raw18761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1115 sourceB1115 sourceC1115 difference raw18761; decide +kernel
    rw [ha]
    exact (canonical18761 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1115 + difference 4 0) (sourceB1115 + difference 0 4) sourceC1115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2935) := by
    have ha : (tripleCharges (sourceA1115 + difference 4 0) (sourceB1115 + difference 0 4) sourceC1115) = raw18762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1115 sourceB1115 sourceC1115 difference raw18762; decide +kernel
    rw [ha]
    exact (canonical18762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1115 + difference 5 0) (sourceB1115 + difference 0 5) sourceC1115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA1115 + difference 5 0) (sourceB1115 + difference 0 5) sourceC1115) = raw18763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1115 sourceB1115 sourceC1115 difference raw18763; decide +kernel
    rw [ha]
    exact (canonical18763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1115 + sourceB1115) sourceC1115) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1115 + sourceB1115) sourceC1115) = raw18764 := by
      apply Matrix.ext; unfold doubleCharges sourceA1115 sourceB1115 sourceC1115 raw18764; decide +kernel
    rw [ha]
    exact (canonical18764 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1115 sourceB1115 sourceC1115
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1115, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1116 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1116 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC1116 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceForm1116 : Integer.Sparse Master := [(Sum.inr 5134, 2), (Sum.inr 5137, 1), (Sum.inr 5167, 1), (Sum.inr 5257, 1), (Sum.inr 5393, 2), (Sum.inr 5395, 2), (Sum.inr 5405, 2), (Sum.inr 5434, 2), (Sum.inr 5460, 1), (Sum.inr 5464, 1), (Sum.inr 5469, 1), (Sum.inr 5472, 1), (Sum.inr 5482, 2), (Sum.inr 5483, 2), (Sum.inr 5486, 2), (Sum.inr 5489, 2), (Sum.inr 5490, 2), (Sum.inr 5498, 1), (Sum.inr 5499, 2)]

theorem sourceEq1116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1116 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1116 + difference 0 1) (sourceB1116 + difference 1 0) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1116 + difference 0 1) (sourceB1116 + difference 1 0) sourceC1116) = raw18765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18765; decide +kernel
    rw [ha]
    exact (canonical18765 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1116 + difference 0 2) (sourceB1116 + difference 2 0) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1116 + difference 0 2) (sourceB1116 + difference 2 0) sourceC1116) = raw18766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18766; decide +kernel
    rw [ha]
    exact (canonical18766 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1116 + difference 0 3) (sourceB1116 + difference 3 0) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA1116 + difference 0 3) (sourceB1116 + difference 3 0) sourceC1116) = raw18767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18767; decide +kernel
    rw [ha]
    exact (canonical18767 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1116 + difference 0 4) (sourceB1116 + difference 4 0) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA1116 + difference 0 4) (sourceB1116 + difference 4 0) sourceC1116) = raw18768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18768; decide +kernel
    rw [ha]
    exact (canonical18768 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1116 + difference 0 5) (sourceB1116 + difference 5 0) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5498) := by
    have ha : (tripleCharges (sourceA1116 + difference 0 5) (sourceB1116 + difference 5 0) sourceC1116) = raw18769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18769; decide +kernel
    rw [ha]
    exact (canonical18769 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1116 + difference 1 0) (sourceB1116 + difference 0 1) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1116 + difference 1 0) (sourceB1116 + difference 0 1) sourceC1116) = raw18770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18770; decide +kernel
    rw [ha]
    exact (canonical18770 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1116 + difference 1 2) (sourceB1116 + difference 2 1) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1116 + difference 1 2) (sourceB1116 + difference 2 1) sourceC1116) = raw13776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw13776; decide +kernel
    rw [ha]
    exact (canonical13776 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1116 + difference 1 3) (sourceB1116 + difference 3 1) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1116 + difference 1 3) (sourceB1116 + difference 3 1) sourceC1116) = raw13777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw13777; decide +kernel
    rw [ha]
    exact (canonical13777 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1116 + difference 1 4) (sourceB1116 + difference 4 1) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1116 + difference 1 4) (sourceB1116 + difference 4 1) sourceC1116) = raw13778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw13778; decide +kernel
    rw [ha]
    exact (canonical13778 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1116 + difference 1 5) (sourceB1116 + difference 5 1) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1116 + difference 1 5) (sourceB1116 + difference 5 1) sourceC1116) = raw13779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw13779; decide +kernel
    rw [ha]
    exact (canonical13779 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1116 + difference 2 0) (sourceB1116 + difference 0 2) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA1116 + difference 2 0) (sourceB1116 + difference 0 2) sourceC1116) = raw13786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw13786; decide +kernel
    rw [ha]
    exact (canonical13786 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1116 + difference 2 1) (sourceB1116 + difference 1 2) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5464) := by
    have ha : (tripleCharges (sourceA1116 + difference 2 1) (sourceB1116 + difference 1 2) sourceC1116) = raw18771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18771; decide +kernel
    rw [ha]
    exact (canonical18771 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1116 + difference 2 3) (sourceB1116 + difference 3 2) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1116 + difference 2 3) (sourceB1116 + difference 3 2) sourceC1116) = raw18772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18772; decide +kernel
    rw [ha]
    exact (canonical18772 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1116 + difference 2 4) (sourceB1116 + difference 4 2) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1116 + difference 2 4) (sourceB1116 + difference 4 2) sourceC1116) = raw18773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18773; decide +kernel
    rw [ha]
    exact (canonical18773 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1116 + difference 2 5) (sourceB1116 + difference 5 2) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1116 + difference 2 5) (sourceB1116 + difference 5 2) sourceC1116) = raw18774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18774; decide +kernel
    rw [ha]
    exact (canonical18774 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1116 + difference 3 0) (sourceB1116 + difference 0 3) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1116 + difference 3 0) (sourceB1116 + difference 0 3) sourceC1116) = raw13791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw13791; decide +kernel
    rw [ha]
    exact (canonical13791 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1116 + difference 3 1) (sourceB1116 + difference 1 3) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA1116 + difference 3 1) (sourceB1116 + difference 1 3) sourceC1116) = raw18775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18775; decide +kernel
    rw [ha]
    exact (canonical18775 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1116 + difference 3 2) (sourceB1116 + difference 2 3) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1116 + difference 3 2) (sourceB1116 + difference 2 3) sourceC1116) = raw18776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18776; decide +kernel
    rw [ha]
    exact (canonical18776 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1116 + difference 3 4) (sourceB1116 + difference 4 3) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1116 + difference 3 4) (sourceB1116 + difference 4 3) sourceC1116) = raw18777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18777; decide +kernel
    rw [ha]
    exact (canonical18777 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1116 + difference 3 5) (sourceB1116 + difference 5 3) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1116 + difference 3 5) (sourceB1116 + difference 5 3) sourceC1116) = raw18778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18778; decide +kernel
    rw [ha]
    exact (canonical18778 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1116 + difference 4 0) (sourceB1116 + difference 0 4) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1116 + difference 4 0) (sourceB1116 + difference 0 4) sourceC1116) = raw13796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw13796; decide +kernel
    rw [ha]
    exact (canonical13796 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1116 + difference 4 1) (sourceB1116 + difference 1 4) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA1116 + difference 4 1) (sourceB1116 + difference 1 4) sourceC1116) = raw18779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18779; decide +kernel
    rw [ha]
    exact (canonical18779 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1116 + difference 4 2) (sourceB1116 + difference 2 4) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1116 + difference 4 2) (sourceB1116 + difference 2 4) sourceC1116) = raw18780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18780; decide +kernel
    rw [ha]
    exact (canonical18780 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1116 + difference 4 3) (sourceB1116 + difference 3 4) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1116 + difference 4 3) (sourceB1116 + difference 3 4) sourceC1116) = raw18781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18781; decide +kernel
    rw [ha]
    exact (canonical18781 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1116 + difference 4 5) (sourceB1116 + difference 5 4) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1116 + difference 4 5) (sourceB1116 + difference 5 4) sourceC1116) = raw18782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18782; decide +kernel
    rw [ha]
    exact (canonical18782 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1116 + difference 5 0) (sourceB1116 + difference 0 5) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA1116 + difference 5 0) (sourceB1116 + difference 0 5) sourceC1116) = raw13801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw13801; decide +kernel
    rw [ha]
    exact (canonical13801 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1116 + difference 5 1) (sourceB1116 + difference 1 5) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA1116 + difference 5 1) (sourceB1116 + difference 1 5) sourceC1116) = raw18783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18783; decide +kernel
    rw [ha]
    exact (canonical18783 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1116 + difference 5 2) (sourceB1116 + difference 2 5) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1116 + difference 5 2) (sourceB1116 + difference 2 5) sourceC1116) = raw18784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18784; decide +kernel
    rw [ha]
    exact (canonical18784 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1116 + difference 5 3) (sourceB1116 + difference 3 5) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1116 + difference 5 3) (sourceB1116 + difference 3 5) sourceC1116) = raw18785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18785; decide +kernel
    rw [ha]
    exact (canonical18785 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1116 + difference 5 4) (sourceB1116 + difference 4 5) sourceC1116) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1116 + difference 5 4) (sourceB1116 + difference 4 5) sourceC1116) = raw18786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1116 sourceB1116 sourceC1116 difference raw18786; decide +kernel
    rw [ha]
    exact (canonical18786 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1116 sourceB1116 sourceC1116
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1116, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1117 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1117 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC1117 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceForm1117 : Integer.Sparse Master := [(Sum.inr 5072, 1), (Sum.inr 5073, 2), (Sum.inr 5098, 1), (Sum.inr 5292, 1), (Sum.inr 5351, 1), (Sum.inr 5352, 2), (Sum.inr 5365, 1), (Sum.inr 5416, 1), (Sum.inr 5424, 2), (Sum.inr 5433, 1), (Sum.inr 5476, 2), (Sum.inr 5477, 2), (Sum.inr 5478, 2), (Sum.inr 5483, 2), (Sum.inr 5485, 1), (Sum.inr 5486, 1), (Sum.inr 5490, 2), (Sum.inr 5493, 1), (Sum.inr 5497, 1), (Sum.inr 5499, 1), (Sum.inr 5500, 2)]

theorem sourceEq1117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1117 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1117 + difference 0 1) (sourceB1117 + difference 1 0) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1117 + difference 0 1) (sourceB1117 + difference 1 0) sourceC1117) = raw18787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18787; decide +kernel
    rw [ha]
    exact (canonical18787 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1117 + difference 0 2) (sourceB1117 + difference 2 0) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5497) := by
    have ha : (tripleCharges (sourceA1117 + difference 0 2) (sourceB1117 + difference 2 0) sourceC1117) = raw18788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18788; decide +kernel
    rw [ha]
    exact (canonical18788 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1117 + difference 0 3) (sourceB1117 + difference 3 0) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA1117 + difference 0 3) (sourceB1117 + difference 3 0) sourceC1117) = raw17585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17585; decide +kernel
    rw [ha]
    exact (canonical17585 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1117 + difference 0 4) (sourceB1117 + difference 4 0) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA1117 + difference 0 4) (sourceB1117 + difference 4 0) sourceC1117) = raw18789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18789; decide +kernel
    rw [ha]
    exact (canonical18789 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1117 + difference 0 5) (sourceB1117 + difference 5 0) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA1117 + difference 0 5) (sourceB1117 + difference 5 0) sourceC1117) = raw18790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18790; decide +kernel
    rw [ha]
    exact (canonical18790 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1117 + difference 1 0) (sourceB1117 + difference 0 1) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1117 + difference 1 0) (sourceB1117 + difference 0 1) sourceC1117) = raw18791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18791; decide +kernel
    rw [ha]
    exact (canonical18791 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1117 + difference 1 2) (sourceB1117 + difference 2 1) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1117 + difference 1 2) (sourceB1117 + difference 2 1) sourceC1117) = raw12592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12592; decide +kernel
    rw [ha]
    exact (canonical12592 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1117 + difference 1 3) (sourceB1117 + difference 3 1) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1117 + difference 1 3) (sourceB1117 + difference 3 1) sourceC1117) = raw12593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12593; decide +kernel
    rw [ha]
    exact (canonical12593 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1117 + difference 1 4) (sourceB1117 + difference 4 1) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1117 + difference 1 4) (sourceB1117 + difference 4 1) sourceC1117) = raw12594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12594; decide +kernel
    rw [ha]
    exact (canonical12594 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1117 + difference 1 5) (sourceB1117 + difference 5 1) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1117 + difference 1 5) (sourceB1117 + difference 5 1) sourceC1117) = raw12595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12595; decide +kernel
    rw [ha]
    exact (canonical12595 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1117 + difference 2 0) (sourceB1117 + difference 0 2) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA1117 + difference 2 0) (sourceB1117 + difference 0 2) sourceC1117) = raw12602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12602; decide +kernel
    rw [ha]
    exact (canonical12602 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1117 + difference 2 1) (sourceB1117 + difference 1 2) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1117 + difference 2 1) (sourceB1117 + difference 1 2) sourceC1117) = raw18792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18792; decide +kernel
    rw [ha]
    exact (canonical18792 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1117 + difference 2 3) (sourceB1117 + difference 3 2) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1117 + difference 2 3) (sourceB1117 + difference 3 2) sourceC1117) = raw17593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17593; decide +kernel
    rw [ha]
    exact (canonical17593 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1117 + difference 2 4) (sourceB1117 + difference 4 2) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1117 + difference 2 4) (sourceB1117 + difference 4 2) sourceC1117) = raw18793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18793; decide +kernel
    rw [ha]
    exact (canonical18793 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1117 + difference 2 5) (sourceB1117 + difference 5 2) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1117 + difference 2 5) (sourceB1117 + difference 5 2) sourceC1117) = raw18794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18794; decide +kernel
    rw [ha]
    exact (canonical18794 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1117 + difference 3 0) (sourceB1117 + difference 0 3) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1117 + difference 3 0) (sourceB1117 + difference 0 3) sourceC1117) = raw12607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12607; decide +kernel
    rw [ha]
    exact (canonical12607 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1117 + difference 3 1) (sourceB1117 + difference 1 3) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1117 + difference 3 1) (sourceB1117 + difference 1 3) sourceC1117) = raw18795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18795; decide +kernel
    rw [ha]
    exact (canonical18795 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1117 + difference 3 2) (sourceB1117 + difference 2 3) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA1117 + difference 3 2) (sourceB1117 + difference 2 3) sourceC1117) = raw18796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18796; decide +kernel
    rw [ha]
    exact (canonical18796 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1117 + difference 3 4) (sourceB1117 + difference 4 3) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1117 + difference 3 4) (sourceB1117 + difference 4 3) sourceC1117) = raw18797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18797; decide +kernel
    rw [ha]
    exact (canonical18797 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1117 + difference 3 5) (sourceB1117 + difference 5 3) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1117 + difference 3 5) (sourceB1117 + difference 5 3) sourceC1117) = raw18798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18798; decide +kernel
    rw [ha]
    exact (canonical18798 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1117 + difference 4 0) (sourceB1117 + difference 0 4) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1117 + difference 4 0) (sourceB1117 + difference 0 4) sourceC1117) = raw12612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12612; decide +kernel
    rw [ha]
    exact (canonical12612 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1117 + difference 4 1) (sourceB1117 + difference 1 4) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1117 + difference 4 1) (sourceB1117 + difference 1 4) sourceC1117) = raw18799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18799; decide +kernel
    rw [ha]
    exact (canonical18799 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1117 + difference 4 2) (sourceB1117 + difference 2 4) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA1117 + difference 4 2) (sourceB1117 + difference 2 4) sourceC1117) = raw18800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18800; decide +kernel
    rw [ha]
    exact (canonical18800 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1117 + difference 4 3) (sourceB1117 + difference 3 4) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1117 + difference 4 3) (sourceB1117 + difference 3 4) sourceC1117) = raw17601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17601; decide +kernel
    rw [ha]
    exact (canonical17601 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1117 + difference 4 5) (sourceB1117 + difference 5 4) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1117 + difference 4 5) (sourceB1117 + difference 5 4) sourceC1117) = raw18801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18801; decide +kernel
    rw [ha]
    exact (canonical18801 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1117 + difference 5 0) (sourceB1117 + difference 0 5) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA1117 + difference 5 0) (sourceB1117 + difference 0 5) sourceC1117) = raw12617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw12617; decide +kernel
    rw [ha]
    exact (canonical12617 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1117 + difference 5 1) (sourceB1117 + difference 1 5) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1117 + difference 5 1) (sourceB1117 + difference 1 5) sourceC1117) = raw17594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17594; decide +kernel
    rw [ha]
    exact (canonical17594 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1117 + difference 5 2) (sourceB1117 + difference 2 5) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1117 + difference 5 2) (sourceB1117 + difference 2 5) sourceC1117) = raw17595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17595; decide +kernel
    rw [ha]
    exact (canonical17595 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1117 + difference 5 3) (sourceB1117 + difference 3 5) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1117 + difference 5 3) (sourceB1117 + difference 3 5) sourceC1117) = raw18802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw18802; decide +kernel
    rw [ha]
    exact (canonical18802 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1117 + difference 5 4) (sourceB1117 + difference 4 5) sourceC1117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1117 + difference 5 4) (sourceB1117 + difference 4 5) sourceC1117) = raw17596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1117 sourceB1117 sourceC1117 difference raw17596; decide +kernel
    rw [ha]
    exact (canonical17596 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1117 sourceB1117 sourceC1117
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1117, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1118 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1118 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1118 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceForm1118 : Integer.Sparse Master := [(Sum.inr 5070, 2), (Sum.inr 5076, 1), (Sum.inr 5093, 1), (Sum.inr 5290, 1), (Sum.inr 5349, 2), (Sum.inr 5354, 1), (Sum.inr 5363, 1), (Sum.inr 5397, 2), (Sum.inr 5401, 2), (Sum.inr 5416, 1), (Sum.inr 5422, 1), (Sum.inr 5431, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5438, 2), (Sum.inr 5450, 1), (Sum.inr 5484, 2), (Sum.inr 5485, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2), (Sum.inr 5492, 2)]

theorem sourceEq1118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1118 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1118 + difference 0 1) (sourceB1118 + difference 1 0) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1118 + difference 0 1) (sourceB1118 + difference 1 0) sourceC1118) = raw18803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18803; decide +kernel
    rw [ha]
    exact (canonical18803 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1118 + difference 0 2) (sourceB1118 + difference 2 0) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1118 + difference 0 2) (sourceB1118 + difference 2 0) sourceC1118) = raw18804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18804; decide +kernel
    rw [ha]
    exact (canonical18804 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1118 + difference 0 3) (sourceB1118 + difference 3 0) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1118 + difference 0 3) (sourceB1118 + difference 3 0) sourceC1118) = raw18805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18805; decide +kernel
    rw [ha]
    exact (canonical18805 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1118 + difference 0 4) (sourceB1118 + difference 4 0) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1118 + difference 0 4) (sourceB1118 + difference 4 0) sourceC1118) = raw18806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18806; decide +kernel
    rw [ha]
    exact (canonical18806 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1118 + difference 0 5) (sourceB1118 + difference 5 0) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1118 + difference 0 5) (sourceB1118 + difference 5 0) sourceC1118) = raw18807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18807; decide +kernel
    rw [ha]
    exact (canonical18807 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1118 + difference 1 0) (sourceB1118 + difference 0 1) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1118 + difference 1 0) (sourceB1118 + difference 0 1) sourceC1118) = raw18808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18808; decide +kernel
    rw [ha]
    exact (canonical18808 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1118 + difference 1 2) (sourceB1118 + difference 2 1) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1118 + difference 1 2) (sourceB1118 + difference 2 1) sourceC1118) = raw18809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18809; decide +kernel
    rw [ha]
    exact (canonical18809 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1118 + difference 1 3) (sourceB1118 + difference 3 1) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1118 + difference 1 3) (sourceB1118 + difference 3 1) sourceC1118) = raw18810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18810; decide +kernel
    rw [ha]
    exact (canonical18810 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1118 + difference 1 4) (sourceB1118 + difference 4 1) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1118 + difference 1 4) (sourceB1118 + difference 4 1) sourceC1118) = raw18811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18811; decide +kernel
    rw [ha]
    exact (canonical18811 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1118 + difference 1 5) (sourceB1118 + difference 5 1) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1118 + difference 1 5) (sourceB1118 + difference 5 1) sourceC1118) = raw18812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18812; decide +kernel
    rw [ha]
    exact (canonical18812 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1118 + difference 2 0) (sourceB1118 + difference 0 2) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5093) := by
    have ha : (tripleCharges (sourceA1118 + difference 2 0) (sourceB1118 + difference 0 2) sourceC1118) = raw18813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18813; decide +kernel
    rw [ha]
    exact (canonical18813 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1118 + difference 2 1) (sourceB1118 + difference 1 2) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA1118 + difference 2 1) (sourceB1118 + difference 1 2) sourceC1118) = raw18814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18814; decide +kernel
    rw [ha]
    exact (canonical18814 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1118 + difference 2 3) (sourceB1118 + difference 3 2) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1118 + difference 2 3) (sourceB1118 + difference 3 2) sourceC1118) = raw18815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18815; decide +kernel
    rw [ha]
    exact (canonical18815 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1118 + difference 2 4) (sourceB1118 + difference 4 2) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1118 + difference 2 4) (sourceB1118 + difference 4 2) sourceC1118) = raw18816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18816; decide +kernel
    rw [ha]
    exact (canonical18816 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1118 + difference 2 5) (sourceB1118 + difference 5 2) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1118 + difference 2 5) (sourceB1118 + difference 5 2) sourceC1118) = raw18817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18817; decide +kernel
    rw [ha]
    exact (canonical18817 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1118 + difference 3 0) (sourceB1118 + difference 0 3) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA1118 + difference 3 0) (sourceB1118 + difference 0 3) sourceC1118) = raw18818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18818; decide +kernel
    rw [ha]
    exact (canonical18818 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1118 + difference 3 1) (sourceB1118 + difference 1 3) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1118 + difference 3 1) (sourceB1118 + difference 1 3) sourceC1118) = raw18819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18819; decide +kernel
    rw [ha]
    exact (canonical18819 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1118 + difference 3 2) (sourceB1118 + difference 2 3) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1118 + difference 3 2) (sourceB1118 + difference 2 3) sourceC1118) = raw18820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18820; decide +kernel
    rw [ha]
    exact (canonical18820 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1118 + difference 3 4) (sourceB1118 + difference 4 3) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1118 + difference 3 4) (sourceB1118 + difference 4 3) sourceC1118) = raw18821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18821; decide +kernel
    rw [ha]
    exact (canonical18821 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1118 + difference 3 5) (sourceB1118 + difference 5 3) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1118 + difference 3 5) (sourceB1118 + difference 5 3) sourceC1118) = raw18822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18822; decide +kernel
    rw [ha]
    exact (canonical18822 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1118 + difference 4 0) (sourceB1118 + difference 0 4) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA1118 + difference 4 0) (sourceB1118 + difference 0 4) sourceC1118) = raw18823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18823; decide +kernel
    rw [ha]
    exact (canonical18823 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1118 + difference 4 1) (sourceB1118 + difference 1 4) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1118 + difference 4 1) (sourceB1118 + difference 1 4) sourceC1118) = raw18824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18824; decide +kernel
    rw [ha]
    exact (canonical18824 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1118 + difference 4 2) (sourceB1118 + difference 2 4) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1118 + difference 4 2) (sourceB1118 + difference 2 4) sourceC1118) = raw18825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18825; decide +kernel
    rw [ha]
    exact (canonical18825 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1118 + difference 4 3) (sourceB1118 + difference 3 4) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1118 + difference 4 3) (sourceB1118 + difference 3 4) sourceC1118) = raw18826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18826; decide +kernel
    rw [ha]
    exact (canonical18826 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1118 + difference 4 5) (sourceB1118 + difference 5 4) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1118 + difference 4 5) (sourceB1118 + difference 5 4) sourceC1118) = raw18827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18827; decide +kernel
    rw [ha]
    exact (canonical18827 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1118 + difference 5 0) (sourceB1118 + difference 0 5) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA1118 + difference 5 0) (sourceB1118 + difference 0 5) sourceC1118) = raw18828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18828; decide +kernel
    rw [ha]
    exact (canonical18828 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1118 + difference 5 1) (sourceB1118 + difference 1 5) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA1118 + difference 5 1) (sourceB1118 + difference 1 5) sourceC1118) = raw18829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18829; decide +kernel
    rw [ha]
    exact (canonical18829 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1118 + difference 5 2) (sourceB1118 + difference 2 5) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1118 + difference 5 2) (sourceB1118 + difference 2 5) sourceC1118) = raw18830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18830; decide +kernel
    rw [ha]
    exact (canonical18830 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1118 + difference 5 3) (sourceB1118 + difference 3 5) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1118 + difference 5 3) (sourceB1118 + difference 3 5) sourceC1118) = raw18831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18831; decide +kernel
    rw [ha]
    exact (canonical18831 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1118 + difference 5 4) (sourceB1118 + difference 4 5) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1118 + difference 5 4) (sourceB1118 + difference 4 5) sourceC1118) = raw18832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18832; decide +kernel
    rw [ha]
    exact (canonical18832 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1118 sourceB1118 sourceC1118
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1118, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1119 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1119 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1119 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceForm1119 : Integer.Sparse Master := [(Sum.inr 2477, 2), (Sum.inr 2483, 1), (Sum.inr 2503, 1), (Sum.inr 2764, 1), (Sum.inr 3687, 2), (Sum.inr 3692, 1), (Sum.inr 3701, 1), (Sum.inr 3787, 2), (Sum.inr 3796, 2), (Sum.inr 3849, 1), (Sum.inr 3876, 2), (Sum.inr 3900, 1), (Sum.inr 3901, 1), (Sum.inr 3910, 1), (Sum.inr 3967, 1), (Sum.inr 3982, 2), (Sum.inr 3983, 2), (Sum.inr 3998, 1), (Sum.inr 4011, 1), (Sum.inr 4013, 2), (Sum.inr 4017, 2)]

theorem sourceEq1119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1119 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1119 + difference 0 1) (sourceB1119 + difference 1 0) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA1119 + difference 0 1) (sourceB1119 + difference 1 0) sourceC1119) = raw18833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18833; decide +kernel
    rw [ha]
    exact (canonical18833 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1119 + difference 0 2) (sourceB1119 + difference 2 0) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4011) := by
    have ha : (tripleCharges (sourceA1119 + difference 0 2) (sourceB1119 + difference 2 0) sourceC1119) = raw18834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18834; decide +kernel
    rw [ha]
    exact (canonical18834 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1119 + difference 0 3) (sourceB1119 + difference 3 0) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA1119 + difference 0 3) (sourceB1119 + difference 3 0) sourceC1119) = raw18835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18835; decide +kernel
    rw [ha]
    exact (canonical18835 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1119 + difference 0 4) (sourceB1119 + difference 4 0) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA1119 + difference 0 4) (sourceB1119 + difference 4 0) sourceC1119) = raw18836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18836; decide +kernel
    rw [ha]
    exact (canonical18836 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1119 + difference 0 5) (sourceB1119 + difference 5 0) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3901) := by
    have ha : (tripleCharges (sourceA1119 + difference 0 5) (sourceB1119 + difference 5 0) sourceC1119) = raw18837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18837; decide +kernel
    rw [ha]
    exact (canonical18837 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1119 + difference 1 0) (sourceB1119 + difference 0 1) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA1119 + difference 1 0) (sourceB1119 + difference 0 1) sourceC1119) = raw18838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18838; decide +kernel
    rw [ha]
    exact (canonical18838 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1119 + difference 1 2) (sourceB1119 + difference 2 1) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA1119 + difference 1 2) (sourceB1119 + difference 2 1) sourceC1119) = raw18839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18839; decide +kernel
    rw [ha]
    exact (canonical18839 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1119 + difference 1 3) (sourceB1119 + difference 3 1) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA1119 + difference 1 3) (sourceB1119 + difference 3 1) sourceC1119) = raw18840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18840; decide +kernel
    rw [ha]
    exact (canonical18840 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1119 + difference 1 4) (sourceB1119 + difference 4 1) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA1119 + difference 1 4) (sourceB1119 + difference 4 1) sourceC1119) = raw18841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18841; decide +kernel
    rw [ha]
    exact (canonical18841 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1119 + difference 1 5) (sourceB1119 + difference 5 1) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA1119 + difference 1 5) (sourceB1119 + difference 5 1) sourceC1119) = raw18842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18842; decide +kernel
    rw [ha]
    exact (canonical18842 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1119 + difference 2 0) (sourceB1119 + difference 0 2) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2503) := by
    have ha : (tripleCharges (sourceA1119 + difference 2 0) (sourceB1119 + difference 0 2) sourceC1119) = raw18843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18843; decide +kernel
    rw [ha]
    exact (canonical18843 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1119 + difference 2 1) (sourceB1119 + difference 1 2) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3701) := by
    have ha : (tripleCharges (sourceA1119 + difference 2 1) (sourceB1119 + difference 1 2) sourceC1119) = raw18844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18844; decide +kernel
    rw [ha]
    exact (canonical18844 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1119 + difference 2 3) (sourceB1119 + difference 3 2) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1119 + difference 2 3) (sourceB1119 + difference 3 2) sourceC1119) = raw18845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18845; decide +kernel
    rw [ha]
    exact (canonical18845 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1119 + difference 2 4) (sourceB1119 + difference 4 2) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1119 + difference 2 4) (sourceB1119 + difference 4 2) sourceC1119) = raw18846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18846; decide +kernel
    rw [ha]
    exact (canonical18846 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1119 + difference 2 5) (sourceB1119 + difference 5 2) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3900) := by
    have ha : (tripleCharges (sourceA1119 + difference 2 5) (sourceB1119 + difference 5 2) sourceC1119) = raw18847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18847; decide +kernel
    rw [ha]
    exact (canonical18847 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1119 + difference 3 0) (sourceB1119 + difference 0 3) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA1119 + difference 3 0) (sourceB1119 + difference 0 3) sourceC1119) = raw18848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18848; decide +kernel
    rw [ha]
    exact (canonical18848 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1119 + difference 3 1) (sourceB1119 + difference 1 3) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3687) := by
    have ha : (tripleCharges (sourceA1119 + difference 3 1) (sourceB1119 + difference 1 3) sourceC1119) = raw18849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18849; decide +kernel
    rw [ha]
    exact (canonical18849 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1119 + difference 3 2) (sourceB1119 + difference 2 3) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA1119 + difference 3 2) (sourceB1119 + difference 2 3) sourceC1119) = raw18850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18850; decide +kernel
    rw [ha]
    exact (canonical18850 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1119 + difference 3 4) (sourceB1119 + difference 4 3) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1119 + difference 3 4) (sourceB1119 + difference 4 3) sourceC1119) = raw18851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18851; decide +kernel
    rw [ha]
    exact (canonical18851 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1119 + difference 3 5) (sourceB1119 + difference 5 3) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1119 + difference 3 5) (sourceB1119 + difference 5 3) sourceC1119) = raw18852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18852; decide +kernel
    rw [ha]
    exact (canonical18852 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1119 + difference 4 0) (sourceB1119 + difference 0 4) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA1119 + difference 4 0) (sourceB1119 + difference 0 4) sourceC1119) = raw18853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18853; decide +kernel
    rw [ha]
    exact (canonical18853 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1119 + difference 4 1) (sourceB1119 + difference 1 4) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3687) := by
    have ha : (tripleCharges (sourceA1119 + difference 4 1) (sourceB1119 + difference 1 4) sourceC1119) = raw18854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18854; decide +kernel
    rw [ha]
    exact (canonical18854 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1119 + difference 4 2) (sourceB1119 + difference 2 4) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA1119 + difference 4 2) (sourceB1119 + difference 2 4) sourceC1119) = raw18855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18855; decide +kernel
    rw [ha]
    exact (canonical18855 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1119 + difference 4 3) (sourceB1119 + difference 3 4) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1119 + difference 4 3) (sourceB1119 + difference 3 4) sourceC1119) = raw18856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18856; decide +kernel
    rw [ha]
    exact (canonical18856 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1119 + difference 4 5) (sourceB1119 + difference 5 4) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1119 + difference 4 5) (sourceB1119 + difference 5 4) sourceC1119) = raw18857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18857; decide +kernel
    rw [ha]
    exact (canonical18857 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1119 + difference 5 0) (sourceB1119 + difference 0 5) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA1119 + difference 5 0) (sourceB1119 + difference 0 5) sourceC1119) = raw18858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18858; decide +kernel
    rw [ha]
    exact (canonical18858 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1119 + difference 5 1) (sourceB1119 + difference 1 5) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA1119 + difference 5 1) (sourceB1119 + difference 1 5) sourceC1119) = raw18859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18859; decide +kernel
    rw [ha]
    exact (canonical18859 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1119 + difference 5 2) (sourceB1119 + difference 2 5) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3967) := by
    have ha : (tripleCharges (sourceA1119 + difference 5 2) (sourceB1119 + difference 2 5) sourceC1119) = raw18860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18860; decide +kernel
    rw [ha]
    exact (canonical18860 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1119 + difference 5 3) (sourceB1119 + difference 3 5) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA1119 + difference 5 3) (sourceB1119 + difference 3 5) sourceC1119) = raw18861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18861; decide +kernel
    rw [ha]
    exact (canonical18861 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1119 + difference 5 4) (sourceB1119 + difference 4 5) sourceC1119) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA1119 + difference 5 4) (sourceB1119 + difference 4 5) sourceC1119) = raw18862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1119 sourceB1119 sourceC1119 difference raw18862; decide +kernel
    rw [ha]
    exact (canonical18862 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1119 sourceB1119 sourceC1119
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1119, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
