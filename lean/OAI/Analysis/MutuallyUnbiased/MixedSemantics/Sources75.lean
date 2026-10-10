import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical95
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical107
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical137
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical145
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical146
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical147
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical148
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical192
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical194
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical201
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical211
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical236
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical237
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical253
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical257
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical258
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical260

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2400 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2400 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2400 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceForm2400 : Integer.Sparse Master := [(Sum.inr 4322, 1), (Sum.inr 4323, 2), (Sum.inr 4344, 1), (Sum.inr 4399, 1), (Sum.inr 4927, 1), (Sum.inr 4928, 2), (Sum.inr 4941, 1), (Sum.inr 4986, 1), (Sum.inr 4987, 2), (Sum.inr 4998, 1), (Sum.inr 5075, 2), (Sum.inr 5134, 2), (Sum.inr 5141, 2), (Sum.inr 5167, 1), (Sum.inr 5169, 2), (Sum.inr 5257, 1), (Sum.inr 5259, 2), (Sum.inr 5460, 1), (Sum.inr 5469, 1), (Sum.inr 5482, 1), (Sum.inr 5483, 2)]

theorem sourceEq2400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2400 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2400 + difference 0 1) (sourceB2400 + difference 1 0) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2400 + difference 0 1) (sourceB2400 + difference 1 0) sourceC2400) = raw18783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw18783; decide +kernel
    rw [ha]
    exact (canonical18783 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2400 + difference 0 2) (sourceB2400 + difference 2 0) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA2400 + difference 0 2) (sourceB2400 + difference 2 0) sourceC2400) = raw18784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw18784; decide +kernel
    rw [ha]
    exact (canonical18784 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2400 + difference 0 3) (sourceB2400 + difference 3 0) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2400 + difference 0 3) (sourceB2400 + difference 3 0) sourceC2400) = raw18785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw18785; decide +kernel
    rw [ha]
    exact (canonical18785 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2400 + difference 0 4) (sourceB2400 + difference 4 0) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2400 + difference 0 4) (sourceB2400 + difference 4 0) sourceC2400) = raw18786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw18786; decide +kernel
    rw [ha]
    exact (canonical18786 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2400 + difference 0 5) (sourceB2400 + difference 5 0) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2400 + difference 0 5) (sourceB2400 + difference 5 0) sourceC2400) = raw13775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13775; decide +kernel
    rw [ha]
    exact (canonical13775 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2400 + difference 1 0) (sourceB2400 + difference 0 1) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA2400 + difference 1 0) (sourceB2400 + difference 0 1) sourceC2400) = raw13800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13800; decide +kernel
    rw [ha]
    exact (canonical13800 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2400 + difference 1 2) (sourceB2400 + difference 2 1) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA2400 + difference 1 2) (sourceB2400 + difference 2 1) sourceC2400) = raw13802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13802; decide +kernel
    rw [ha]
    exact (canonical13802 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2400 + difference 1 3) (sourceB2400 + difference 3 1) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2400 + difference 1 3) (sourceB2400 + difference 3 1) sourceC2400) = raw13803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13803; decide +kernel
    rw [ha]
    exact (canonical13803 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2400 + difference 1 4) (sourceB2400 + difference 4 1) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2400 + difference 1 4) (sourceB2400 + difference 4 1) sourceC2400) = raw13804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13804; decide +kernel
    rw [ha]
    exact (canonical13804 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2400 + difference 1 5) (sourceB2400 + difference 5 1) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2400 + difference 1 5) (sourceB2400 + difference 5 1) sourceC2400) = raw18770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw18770; decide +kernel
    rw [ha]
    exact (canonical18770 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2400 + difference 2 0) (sourceB2400 + difference 0 2) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA2400 + difference 2 0) (sourceB2400 + difference 0 2) sourceC2400) = raw32881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32881; decide +kernel
    rw [ha]
    exact (canonical32881 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2400 + difference 2 1) (sourceB2400 + difference 1 2) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2400 + difference 2 1) (sourceB2400 + difference 1 2) sourceC2400) = raw32882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32882; decide +kernel
    rw [ha]
    exact (canonical32882 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2400 + difference 2 3) (sourceB2400 + difference 3 2) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2400 + difference 2 3) (sourceB2400 + difference 3 2) sourceC2400) = raw32883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32883; decide +kernel
    rw [ha]
    exact (canonical32883 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2400 + difference 2 4) (sourceB2400 + difference 4 2) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2400 + difference 2 4) (sourceB2400 + difference 4 2) sourceC2400) = raw32884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32884; decide +kernel
    rw [ha]
    exact (canonical32884 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2400 + difference 2 5) (sourceB2400 + difference 5 2) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2400 + difference 2 5) (sourceB2400 + difference 5 2) sourceC2400) = raw13786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13786; decide +kernel
    rw [ha]
    exact (canonical13786 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2400 + difference 3 0) (sourceB2400 + difference 0 3) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2400 + difference 3 0) (sourceB2400 + difference 0 3) sourceC2400) = raw32885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32885; decide +kernel
    rw [ha]
    exact (canonical32885 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2400 + difference 3 1) (sourceB2400 + difference 1 3) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2400 + difference 3 1) (sourceB2400 + difference 1 3) sourceC2400) = raw32886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32886; decide +kernel
    rw [ha]
    exact (canonical32886 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2400 + difference 3 2) (sourceB2400 + difference 2 3) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2400 + difference 3 2) (sourceB2400 + difference 2 3) sourceC2400) = raw32887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32887; decide +kernel
    rw [ha]
    exact (canonical32887 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2400 + difference 3 4) (sourceB2400 + difference 4 3) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2400 + difference 3 4) (sourceB2400 + difference 4 3) sourceC2400) = raw32888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32888; decide +kernel
    rw [ha]
    exact (canonical32888 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2400 + difference 3 5) (sourceB2400 + difference 5 3) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2400 + difference 3 5) (sourceB2400 + difference 5 3) sourceC2400) = raw13791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13791; decide +kernel
    rw [ha]
    exact (canonical13791 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2400 + difference 4 0) (sourceB2400 + difference 0 4) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2400 + difference 4 0) (sourceB2400 + difference 0 4) sourceC2400) = raw32889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32889; decide +kernel
    rw [ha]
    exact (canonical32889 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2400 + difference 4 1) (sourceB2400 + difference 1 4) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2400 + difference 4 1) (sourceB2400 + difference 1 4) sourceC2400) = raw32890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32890; decide +kernel
    rw [ha]
    exact (canonical32890 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2400 + difference 4 2) (sourceB2400 + difference 2 4) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2400 + difference 4 2) (sourceB2400 + difference 2 4) sourceC2400) = raw32891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32891; decide +kernel
    rw [ha]
    exact (canonical32891 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2400 + difference 4 3) (sourceB2400 + difference 3 4) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2400 + difference 4 3) (sourceB2400 + difference 3 4) sourceC2400) = raw32892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32892; decide +kernel
    rw [ha]
    exact (canonical32892 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2400 + difference 4 5) (sourceB2400 + difference 5 4) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2400 + difference 4 5) (sourceB2400 + difference 5 4) sourceC2400) = raw13796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13796; decide +kernel
    rw [ha]
    exact (canonical13796 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2400 + difference 5 0) (sourceB2400 + difference 0 5) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4322) := by
    have ha : (tripleCharges (sourceA2400 + difference 5 0) (sourceB2400 + difference 0 5) sourceC2400) = raw32893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32893; decide +kernel
    rw [ha]
    exact (canonical32893 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2400 + difference 5 1) (sourceB2400 + difference 1 5) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4927) := by
    have ha : (tripleCharges (sourceA2400 + difference 5 1) (sourceB2400 + difference 1 5) sourceC2400) = raw32894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32894; decide +kernel
    rw [ha]
    exact (canonical32894 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2400 + difference 5 2) (sourceB2400 + difference 2 5) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4986) := by
    have ha : (tripleCharges (sourceA2400 + difference 5 2) (sourceB2400 + difference 2 5) sourceC2400) = raw32895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32895; decide +kernel
    rw [ha]
    exact (canonical32895 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2400 + difference 5 3) (sourceB2400 + difference 3 5) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2400 + difference 5 3) (sourceB2400 + difference 3 5) sourceC2400) = raw32896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32896; decide +kernel
    rw [ha]
    exact (canonical32896 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2400 + difference 5 4) (sourceB2400 + difference 4 5) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2400 + difference 5 4) (sourceB2400 + difference 4 5) sourceC2400) = raw32897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32897; decide +kernel
    rw [ha]
    exact (canonical32897 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2400 sourceB2400 sourceC2400
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2400, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2401 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceB2401 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2401 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2401 : Integer.Sparse Master := [(Sum.inr 4786, 1), (Sum.inr 4787, 2), (Sum.inr 4826, 1), (Sum.inr 4838, 1), (Sum.inr 5058, 1), (Sum.inr 5059, 2), (Sum.inr 5072, 1), (Sum.inr 5073, 2), (Sum.inr 5085, 1), (Sum.inr 5104, 1), (Sum.inr 5123, 1), (Sum.inr 5124, 2), (Sum.inr 5134, 2), (Sum.inr 5135, 2), (Sum.inr 5138, 2), (Sum.inr 5148, 1), (Sum.inr 5169, 2), (Sum.inr 5172, 1), (Sum.inr 5179, 1), (Sum.inr 5185, 2), (Sum.inr 5187, 1)]

theorem sourceEq2401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2401 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2401 + difference 0 1) (sourceB2401 + difference 1 0) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2401 + difference 0 1) (sourceB2401 + difference 1 0) sourceC2401) = raw32898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32898; decide +kernel
    rw [ha]
    exact (canonical32898 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2401 + difference 0 2) (sourceB2401 + difference 2 0) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA2401 + difference 0 2) (sourceB2401 + difference 2 0) sourceC2401) = raw32899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32899; decide +kernel
    rw [ha]
    exact (canonical32899 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2401 + difference 0 3) (sourceB2401 + difference 3 0) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2401 + difference 0 3) (sourceB2401 + difference 3 0) sourceC2401) = raw32900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32900; decide +kernel
    rw [ha]
    exact (canonical32900 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2401 + difference 0 4) (sourceB2401 + difference 4 0) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2401 + difference 0 4) (sourceB2401 + difference 4 0) sourceC2401) = raw32901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32901; decide +kernel
    rw [ha]
    exact (canonical32901 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2401 + difference 0 5) (sourceB2401 + difference 5 0) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2401 + difference 0 5) (sourceB2401 + difference 5 0) sourceC2401) = raw32226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32226; decide +kernel
    rw [ha]
    exact (canonical32226 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2401 + difference 1 0) (sourceB2401 + difference 0 1) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2401 + difference 1 0) (sourceB2401 + difference 0 1) sourceC2401) = raw32902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32902; decide +kernel
    rw [ha]
    exact (canonical32902 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2401 + difference 1 2) (sourceB2401 + difference 2 1) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5179) := by
    have ha : (tripleCharges (sourceA2401 + difference 1 2) (sourceB2401 + difference 2 1) sourceC2401) = raw32903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32903; decide +kernel
    rw [ha]
    exact (canonical32903 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2401 + difference 1 3) (sourceB2401 + difference 3 1) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2401 + difference 1 3) (sourceB2401 + difference 3 1) sourceC2401) = raw32904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32904; decide +kernel
    rw [ha]
    exact (canonical32904 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2401 + difference 1 4) (sourceB2401 + difference 4 1) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2401 + difference 1 4) (sourceB2401 + difference 4 1) sourceC2401) = raw32905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32905; decide +kernel
    rw [ha]
    exact (canonical32905 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2401 + difference 1 5) (sourceB2401 + difference 5 1) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA2401 + difference 1 5) (sourceB2401 + difference 5 1) sourceC2401) = raw32231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32231; decide +kernel
    rw [ha]
    exact (canonical32231 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2401 + difference 2 0) (sourceB2401 + difference 0 2) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2401 + difference 2 0) (sourceB2401 + difference 0 2) sourceC2401) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2401 + difference 2 1) (sourceB2401 + difference 1 2) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2401 + difference 2 1) (sourceB2401 + difference 1 2) sourceC2401) = raw32251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32251; decide +kernel
    rw [ha]
    exact (canonical32251 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2401 + difference 2 3) (sourceB2401 + difference 3 2) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2401 + difference 2 3) (sourceB2401 + difference 3 2) sourceC2401) = raw32253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32253; decide +kernel
    rw [ha]
    exact (canonical32253 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2401 + difference 2 4) (sourceB2401 + difference 4 2) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2401 + difference 2 4) (sourceB2401 + difference 4 2) sourceC2401) = raw32254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32254; decide +kernel
    rw [ha]
    exact (canonical32254 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2401 + difference 2 5) (sourceB2401 + difference 5 2) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2401 + difference 2 5) (sourceB2401 + difference 5 2) sourceC2401) = raw32487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32487; decide +kernel
    rw [ha]
    exact (canonical32487 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2401 + difference 3 0) (sourceB2401 + difference 0 3) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2401 + difference 3 0) (sourceB2401 + difference 0 3) sourceC2401) = raw32906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32906; decide +kernel
    rw [ha]
    exact (canonical32906 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2401 + difference 3 1) (sourceB2401 + difference 1 3) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA2401 + difference 3 1) (sourceB2401 + difference 1 3) sourceC2401) = raw32907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32907; decide +kernel
    rw [ha]
    exact (canonical32907 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2401 + difference 3 2) (sourceB2401 + difference 2 3) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5124) := by
    have ha : (tripleCharges (sourceA2401 + difference 3 2) (sourceB2401 + difference 2 3) sourceC2401) = raw32908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32908; decide +kernel
    rw [ha]
    exact (canonical32908 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2401 + difference 3 4) (sourceB2401 + difference 4 3) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA2401 + difference 3 4) (sourceB2401 + difference 4 3) sourceC2401) = raw32909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32909; decide +kernel
    rw [ha]
    exact (canonical32909 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2401 + difference 3 5) (sourceB2401 + difference 5 3) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2401 + difference 3 5) (sourceB2401 + difference 5 3) sourceC2401) = raw32242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32242; decide +kernel
    rw [ha]
    exact (canonical32242 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2401 + difference 4 0) (sourceB2401 + difference 0 4) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2401 + difference 4 0) (sourceB2401 + difference 0 4) sourceC2401) = raw32910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32910; decide +kernel
    rw [ha]
    exact (canonical32910 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2401 + difference 4 1) (sourceB2401 + difference 1 4) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA2401 + difference 4 1) (sourceB2401 + difference 1 4) sourceC2401) = raw32911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32911; decide +kernel
    rw [ha]
    exact (canonical32911 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2401 + difference 4 2) (sourceB2401 + difference 2 4) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5124) := by
    have ha : (tripleCharges (sourceA2401 + difference 4 2) (sourceB2401 + difference 2 4) sourceC2401) = raw32912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32912; decide +kernel
    rw [ha]
    exact (canonical32912 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2401 + difference 4 3) (sourceB2401 + difference 3 4) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA2401 + difference 4 3) (sourceB2401 + difference 3 4) sourceC2401) = raw32913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32913; decide +kernel
    rw [ha]
    exact (canonical32913 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2401 + difference 4 5) (sourceB2401 + difference 5 4) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2401 + difference 4 5) (sourceB2401 + difference 5 4) sourceC2401) = raw32247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32247; decide +kernel
    rw [ha]
    exact (canonical32247 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2401 + difference 5 0) (sourceB2401 + difference 0 5) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4786) := by
    have ha : (tripleCharges (sourceA2401 + difference 5 0) (sourceB2401 + difference 0 5) sourceC2401) = raw32914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32914; decide +kernel
    rw [ha]
    exact (canonical32914 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2401 + difference 5 1) (sourceB2401 + difference 1 5) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5058) := by
    have ha : (tripleCharges (sourceA2401 + difference 5 1) (sourceB2401 + difference 1 5) sourceC2401) = raw32915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32915; decide +kernel
    rw [ha]
    exact (canonical32915 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2401 + difference 5 2) (sourceB2401 + difference 2 5) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2401 + difference 5 2) (sourceB2401 + difference 2 5) sourceC2401) = raw32916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32916; decide +kernel
    rw [ha]
    exact (canonical32916 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2401 + difference 5 3) (sourceB2401 + difference 3 5) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2401 + difference 5 3) (sourceB2401 + difference 3 5) sourceC2401) = raw32917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32917; decide +kernel
    rw [ha]
    exact (canonical32917 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2401 + difference 5 4) (sourceB2401 + difference 4 5) sourceC2401) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2401 + difference 5 4) (sourceB2401 + difference 4 5) sourceC2401) = raw32837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2401 sourceB2401 sourceC2401 difference raw32837; decide +kernel
    rw [ha]
    exact (canonical32837 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2401 sourceB2401 sourceC2401
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2401, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2402 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2402 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2402 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceForm2402 : Integer.Sparse Master := [(Sum.inr 4528, 1), (Sum.inr 4529, 1), (Sum.inr 4533, 1), (Sum.inr 4545, 1), (Sum.inr 4602, 1), (Sum.inr 4954, 1), (Sum.inr 4955, 1), (Sum.inr 4957, 1), (Sum.inr 4963, 1), (Sum.inr 5033, 1), (Sum.inr 5036, 1), (Sum.inr 5038, 1), (Sum.inr 5075, 1), (Sum.inr 5101, 1), (Sum.inr 5127, 1), (Sum.inr 5129, 1), (Sum.inr 5135, 1), (Sum.inr 5138, 1), (Sum.inr 5141, 1), (Sum.inr 5144, 1), (Sum.inr 5160, 1), (Sum.inr 5163, 1), (Sum.inr 5258, 1), (Sum.inr 5271, 1), (Sum.inr 5274, 1), (Sum.inr 5378, 1), (Sum.inr 5394, 1), (Sum.inr 5409, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1)]

theorem sourceEq2402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2402 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2402 + difference 0 1) (sourceB2402 + difference 1 0) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2402 + difference 0 1) (sourceB2402 + difference 1 0) sourceC2402) = raw32918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32918; decide +kernel
    rw [ha]
    exact (canonical32918 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2402 + difference 0 2) (sourceB2402 + difference 2 0) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA2402 + difference 0 2) (sourceB2402 + difference 2 0) sourceC2402) = raw32919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32919; decide +kernel
    rw [ha]
    exact (canonical32919 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2402 + difference 0 3) (sourceB2402 + difference 3 0) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2402 + difference 0 3) (sourceB2402 + difference 3 0) sourceC2402) = raw32920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32920; decide +kernel
    rw [ha]
    exact (canonical32920 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2402 + difference 0 4) (sourceB2402 + difference 4 0) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2402 + difference 0 4) (sourceB2402 + difference 4 0) sourceC2402) = raw32921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32921; decide +kernel
    rw [ha]
    exact (canonical32921 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2402 + difference 0 5) (sourceB2402 + difference 5 0) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2402 + difference 0 5) (sourceB2402 + difference 5 0) sourceC2402) = raw32922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32922; decide +kernel
    rw [ha]
    exact (canonical32922 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2402 + difference 1 0) (sourceB2402 + difference 0 1) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA2402 + difference 1 0) (sourceB2402 + difference 0 1) sourceC2402) = raw32923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32923; decide +kernel
    rw [ha]
    exact (canonical32923 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2402 + difference 1 2) (sourceB2402 + difference 2 1) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2402 + difference 1 2) (sourceB2402 + difference 2 1) sourceC2402) = raw24651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw24651; decide +kernel
    rw [ha]
    exact (canonical24651 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2402 + difference 1 3) (sourceB2402 + difference 3 1) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2402 + difference 1 3) (sourceB2402 + difference 3 1) sourceC2402) = raw24652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw24652; decide +kernel
    rw [ha]
    exact (canonical24652 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2402 + difference 1 4) (sourceB2402 + difference 4 1) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2402 + difference 1 4) (sourceB2402 + difference 4 1) sourceC2402) = raw24653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw24653; decide +kernel
    rw [ha]
    exact (canonical24653 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2402 + difference 1 5) (sourceB2402 + difference 5 1) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2402 + difference 1 5) (sourceB2402 + difference 5 1) sourceC2402) = raw24654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw24654; decide +kernel
    rw [ha]
    exact (canonical24654 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2402 + difference 2 0) (sourceB2402 + difference 0 2) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4545) := by
    have ha : (tripleCharges (sourceA2402 + difference 2 0) (sourceB2402 + difference 0 2) sourceC2402) = raw24661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw24661; decide +kernel
    rw [ha]
    exact (canonical24661 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2402 + difference 2 1) (sourceB2402 + difference 1 2) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4963) := by
    have ha : (tripleCharges (sourceA2402 + difference 2 1) (sourceB2402 + difference 1 2) sourceC2402) = raw32924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32924; decide +kernel
    rw [ha]
    exact (canonical32924 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2402 + difference 2 3) (sourceB2402 + difference 3 2) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA2402 + difference 2 3) (sourceB2402 + difference 3 2) sourceC2402) = raw32925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32925; decide +kernel
    rw [ha]
    exact (canonical32925 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2402 + difference 2 4) (sourceB2402 + difference 4 2) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2402 + difference 2 4) (sourceB2402 + difference 4 2) sourceC2402) = raw32926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32926; decide +kernel
    rw [ha]
    exact (canonical32926 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2402 + difference 2 5) (sourceB2402 + difference 5 2) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA2402 + difference 2 5) (sourceB2402 + difference 5 2) sourceC2402) = raw32927 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32927; decide +kernel
    rw [ha]
    exact (canonical32927 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2402 + difference 3 0) (sourceB2402 + difference 0 3) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4533) := by
    have ha : (tripleCharges (sourceA2402 + difference 3 0) (sourceB2402 + difference 0 3) sourceC2402) = raw24666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw24666; decide +kernel
    rw [ha]
    exact (canonical24666 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2402 + difference 3 1) (sourceB2402 + difference 1 3) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4955) := by
    have ha : (tripleCharges (sourceA2402 + difference 3 1) (sourceB2402 + difference 1 3) sourceC2402) = raw32928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32928; decide +kernel
    rw [ha]
    exact (canonical32928 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2402 + difference 3 2) (sourceB2402 + difference 2 3) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2402 + difference 3 2) (sourceB2402 + difference 2 3) sourceC2402) = raw32929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32929; decide +kernel
    rw [ha]
    exact (canonical32929 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2402 + difference 3 4) (sourceB2402 + difference 4 3) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2402 + difference 3 4) (sourceB2402 + difference 4 3) sourceC2402) = raw32930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32930; decide +kernel
    rw [ha]
    exact (canonical32930 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2402 + difference 3 5) (sourceB2402 + difference 5 3) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA2402 + difference 3 5) (sourceB2402 + difference 5 3) sourceC2402) = raw32931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32931; decide +kernel
    rw [ha]
    exact (canonical32931 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2402 + difference 4 0) (sourceB2402 + difference 0 4) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4529) := by
    have ha : (tripleCharges (sourceA2402 + difference 4 0) (sourceB2402 + difference 0 4) sourceC2402) = raw24671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw24671; decide +kernel
    rw [ha]
    exact (canonical24671 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2402 + difference 4 1) (sourceB2402 + difference 1 4) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4957) := by
    have ha : (tripleCharges (sourceA2402 + difference 4 1) (sourceB2402 + difference 1 4) sourceC2402) = raw32932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32932; decide +kernel
    rw [ha]
    exact (canonical32932 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2402 + difference 4 2) (sourceB2402 + difference 2 4) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2402 + difference 4 2) (sourceB2402 + difference 2 4) sourceC2402) = raw32933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32933; decide +kernel
    rw [ha]
    exact (canonical32933 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2402 + difference 4 3) (sourceB2402 + difference 3 4) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2402 + difference 4 3) (sourceB2402 + difference 3 4) sourceC2402) = raw32934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32934; decide +kernel
    rw [ha]
    exact (canonical32934 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2402 + difference 4 5) (sourceB2402 + difference 5 4) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2402 + difference 4 5) (sourceB2402 + difference 5 4) sourceC2402) = raw32935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32935; decide +kernel
    rw [ha]
    exact (canonical32935 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2402 + difference 5 0) (sourceB2402 + difference 0 5) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4528) := by
    have ha : (tripleCharges (sourceA2402 + difference 5 0) (sourceB2402 + difference 0 5) sourceC2402) = raw24676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw24676; decide +kernel
    rw [ha]
    exact (canonical24676 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2402 + difference 5 1) (sourceB2402 + difference 1 5) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4954) := by
    have ha : (tripleCharges (sourceA2402 + difference 5 1) (sourceB2402 + difference 1 5) sourceC2402) = raw32936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32936; decide +kernel
    rw [ha]
    exact (canonical32936 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2402 + difference 5 2) (sourceB2402 + difference 2 5) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5033) := by
    have ha : (tripleCharges (sourceA2402 + difference 5 2) (sourceB2402 + difference 2 5) sourceC2402) = raw32937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32937; decide +kernel
    rw [ha]
    exact (canonical32937 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2402 + difference 5 3) (sourceB2402 + difference 3 5) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA2402 + difference 5 3) (sourceB2402 + difference 3 5) sourceC2402) = raw32938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32938; decide +kernel
    rw [ha]
    exact (canonical32938 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2402 + difference 5 4) (sourceB2402 + difference 4 5) sourceC2402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2402 + difference 5 4) (sourceB2402 + difference 4 5) sourceC2402) = raw32939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2402 sourceB2402 sourceC2402 difference raw32939; decide +kernel
    rw [ha]
    exact (canonical32939 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2402 sourceB2402 sourceC2402
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2402, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2403 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2403 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2403 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceForm2403 : Integer.Sparse Master := [(Sum.inr 3258, 1), (Sum.inr 3259, 1), (Sum.inr 3260, 1), (Sum.inr 3267, 1), (Sum.inr 3293, 1), (Sum.inr 3449, 1), (Sum.inr 3450, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3468, 1), (Sum.inr 3470, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3513, 1), (Sum.inr 3515, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3522, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3547, 1), (Sum.inr 3553, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3564, 1), (Sum.inr 3793, 1), (Sum.inr 3795, 1), (Sum.inr 3807, 1), (Sum.inr 3837, 1), (Sum.inr 3838, 1)]

theorem sourceEq2403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2403 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2403 + difference 0 1) (sourceB2403 + difference 1 0) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2403 + difference 0 1) (sourceB2403 + difference 1 0) sourceC2403) = raw32940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32940; decide +kernel
    rw [ha]
    exact (canonical32940 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2403 + difference 0 2) (sourceB2403 + difference 2 0) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA2403 + difference 0 2) (sourceB2403 + difference 2 0) sourceC2403) = raw32941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32941; decide +kernel
    rw [ha]
    exact (canonical32941 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2403 + difference 0 3) (sourceB2403 + difference 3 0) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA2403 + difference 0 3) (sourceB2403 + difference 3 0) sourceC2403) = raw32942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32942; decide +kernel
    rw [ha]
    exact (canonical32942 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2403 + difference 0 4) (sourceB2403 + difference 4 0) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2403 + difference 0 4) (sourceB2403 + difference 4 0) sourceC2403) = raw32943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32943; decide +kernel
    rw [ha]
    exact (canonical32943 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2403 + difference 0 5) (sourceB2403 + difference 5 0) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA2403 + difference 0 5) (sourceB2403 + difference 5 0) sourceC2403) = raw32944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32944; decide +kernel
    rw [ha]
    exact (canonical32944 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2403 + difference 1 0) (sourceB2403 + difference 0 1) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA2403 + difference 1 0) (sourceB2403 + difference 0 1) sourceC2403) = raw32945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32945; decide +kernel
    rw [ha]
    exact (canonical32945 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2403 + difference 1 2) (sourceB2403 + difference 2 1) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2403 + difference 1 2) (sourceB2403 + difference 2 1) sourceC2403) = raw24711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24711; decide +kernel
    rw [ha]
    exact (canonical24711 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2403 + difference 1 3) (sourceB2403 + difference 3 1) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA2403 + difference 1 3) (sourceB2403 + difference 3 1) sourceC2403) = raw24712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24712; decide +kernel
    rw [ha]
    exact (canonical24712 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2403 + difference 1 4) (sourceB2403 + difference 4 1) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA2403 + difference 1 4) (sourceB2403 + difference 4 1) sourceC2403) = raw24713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24713; decide +kernel
    rw [ha]
    exact (canonical24713 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2403 + difference 1 5) (sourceB2403 + difference 5 1) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA2403 + difference 1 5) (sourceB2403 + difference 5 1) sourceC2403) = raw24714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24714; decide +kernel
    rw [ha]
    exact (canonical24714 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2403 + difference 2 0) (sourceB2403 + difference 0 2) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3259) := by
    have ha : (tripleCharges (sourceA2403 + difference 2 0) (sourceB2403 + difference 0 2) sourceC2403) = raw24721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24721; decide +kernel
    rw [ha]
    exact (canonical24721 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2403 + difference 2 1) (sourceB2403 + difference 1 2) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3553) := by
    have ha : (tripleCharges (sourceA2403 + difference 2 1) (sourceB2403 + difference 1 2) sourceC2403) = raw32946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32946; decide +kernel
    rw [ha]
    exact (canonical32946 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2403 + difference 2 3) (sourceB2403 + difference 3 2) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA2403 + difference 2 3) (sourceB2403 + difference 3 2) sourceC2403) = raw32947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32947; decide +kernel
    rw [ha]
    exact (canonical32947 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2403 + difference 2 4) (sourceB2403 + difference 4 2) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2403 + difference 2 4) (sourceB2403 + difference 4 2) sourceC2403) = raw32948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32948; decide +kernel
    rw [ha]
    exact (canonical32948 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2403 + difference 2 5) (sourceB2403 + difference 5 2) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA2403 + difference 2 5) (sourceB2403 + difference 5 2) sourceC2403) = raw32949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32949; decide +kernel
    rw [ha]
    exact (canonical32949 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2403 + difference 3 0) (sourceB2403 + difference 0 3) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA2403 + difference 3 0) (sourceB2403 + difference 0 3) sourceC2403) = raw24726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24726; decide +kernel
    rw [ha]
    exact (canonical24726 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2403 + difference 3 1) (sourceB2403 + difference 1 3) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2403 + difference 3 1) (sourceB2403 + difference 1 3) sourceC2403) = raw32950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32950; decide +kernel
    rw [ha]
    exact (canonical32950 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2403 + difference 3 2) (sourceB2403 + difference 2 3) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3450) := by
    have ha : (tripleCharges (sourceA2403 + difference 3 2) (sourceB2403 + difference 2 3) sourceC2403) = raw32951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32951; decide +kernel
    rw [ha]
    exact (canonical32951 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2403 + difference 3 4) (sourceB2403 + difference 4 3) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2403 + difference 3 4) (sourceB2403 + difference 4 3) sourceC2403) = raw32952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32952; decide +kernel
    rw [ha]
    exact (canonical32952 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2403 + difference 3 5) (sourceB2403 + difference 5 3) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA2403 + difference 3 5) (sourceB2403 + difference 5 3) sourceC2403) = raw32953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32953; decide +kernel
    rw [ha]
    exact (canonical32953 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2403 + difference 4 0) (sourceB2403 + difference 0 4) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA2403 + difference 4 0) (sourceB2403 + difference 0 4) sourceC2403) = raw24731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24731; decide +kernel
    rw [ha]
    exact (canonical24731 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2403 + difference 4 1) (sourceB2403 + difference 1 4) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3509) := by
    have ha : (tripleCharges (sourceA2403 + difference 4 1) (sourceB2403 + difference 1 4) sourceC2403) = raw32954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32954; decide +kernel
    rw [ha]
    exact (canonical32954 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2403 + difference 4 2) (sourceB2403 + difference 2 4) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3453) := by
    have ha : (tripleCharges (sourceA2403 + difference 4 2) (sourceB2403 + difference 2 4) sourceC2403) = raw32955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32955; decide +kernel
    rw [ha]
    exact (canonical32955 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2403 + difference 4 3) (sourceB2403 + difference 3 4) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2403 + difference 4 3) (sourceB2403 + difference 3 4) sourceC2403) = raw32956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32956; decide +kernel
    rw [ha]
    exact (canonical32956 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2403 + difference 4 5) (sourceB2403 + difference 5 4) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA2403 + difference 4 5) (sourceB2403 + difference 5 4) sourceC2403) = raw32957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32957; decide +kernel
    rw [ha]
    exact (canonical32957 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2403 + difference 5 0) (sourceB2403 + difference 0 5) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA2403 + difference 5 0) (sourceB2403 + difference 0 5) sourceC2403) = raw24736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw24736; decide +kernel
    rw [ha]
    exact (canonical24736 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2403 + difference 5 1) (sourceB2403 + difference 1 5) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2403 + difference 5 1) (sourceB2403 + difference 1 5) sourceC2403) = raw32958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32958; decide +kernel
    rw [ha]
    exact (canonical32958 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2403 + difference 5 2) (sourceB2403 + difference 2 5) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3449) := by
    have ha : (tripleCharges (sourceA2403 + difference 5 2) (sourceB2403 + difference 2 5) sourceC2403) = raw32959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32959; decide +kernel
    rw [ha]
    exact (canonical32959 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2403 + difference 5 3) (sourceB2403 + difference 3 5) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA2403 + difference 5 3) (sourceB2403 + difference 3 5) sourceC2403) = raw32960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32960; decide +kernel
    rw [ha]
    exact (canonical32960 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2403 + difference 5 4) (sourceB2403 + difference 4 5) sourceC2403) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2403 + difference 5 4) (sourceB2403 + difference 4 5) sourceC2403) = raw32961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2403 sourceB2403 sourceC2403 difference raw32961; decide +kernel
    rw [ha]
    exact (canonical32961 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2403 sourceB2403 sourceC2403
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2403, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2404 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2404 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2404 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceForm2404 : Integer.Sparse Master := [(Sum.inr 2347, 1), (Sum.inr 2348, 1), (Sum.inr 2350, 1), (Sum.inr 2353, 1), (Sum.inr 2553, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

theorem sourceEq2404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2404 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2404 + difference 0 1) (sourceB2404 + difference 1 0) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2404 + difference 0 1) (sourceB2404 + difference 1 0) sourceC2404) = raw32962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw32962; decide +kernel
    rw [ha]
    exact (canonical32962 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2404 + difference 1 1) (sourceB2404 + difference 1 1) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2404 + difference 1 1) (sourceB2404 + difference 1 1) sourceC2404) = raw24747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw24747; decide +kernel
    rw [ha]
    exact (canonical24747 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2404 + difference 2 1) (sourceB2404 + difference 1 2) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2353) := by
    have ha : (tripleCharges (sourceA2404 + difference 2 1) (sourceB2404 + difference 1 2) sourceC2404) = raw32963 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw32963; decide +kernel
    rw [ha]
    exact (canonical32963 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2404 + difference 3 1) (sourceB2404 + difference 1 3) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2348) := by
    have ha : (tripleCharges (sourceA2404 + difference 3 1) (sourceB2404 + difference 1 3) sourceC2404) = raw32964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw32964; decide +kernel
    rw [ha]
    exact (canonical32964 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2404 + difference 4 1) (sourceB2404 + difference 1 4) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2350) := by
    have ha : (tripleCharges (sourceA2404 + difference 4 1) (sourceB2404 + difference 1 4) sourceC2404) = raw29460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw29460; decide +kernel
    rw [ha]
    exact (canonical29460 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2404 + difference 5 1) (sourceB2404 + difference 1 5) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2347) := by
    have ha : (tripleCharges (sourceA2404 + difference 5 1) (sourceB2404 + difference 1 5) sourceC2404) = raw32965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw32965; decide +kernel
    rw [ha]
    exact (canonical32965 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2404 + sourceB2404) sourceC2404) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2404 + sourceB2404) sourceC2404) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA2404 sourceB2404 sourceC2404 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2404 sourceB2404 sourceC2404
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2404, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2405 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2405 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2405 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceForm2405 : Integer.Sparse Master := [(Sum.inr 4320, 1), (Sum.inr 4321, 1), (Sum.inr 4323, 1), (Sum.inr 4341, 1), (Sum.inr 4396, 1), (Sum.inr 4706, 1), (Sum.inr 4709, 1), (Sum.inr 4728, 1), (Sum.inr 4804, 1), (Sum.inr 4926, 1), (Sum.inr 4928, 1), (Sum.inr 4939, 1), (Sum.inr 4985, 1), (Sum.inr 4987, 1), (Sum.inr 4996, 1), (Sum.inr 5126, 1), (Sum.inr 5134, 2), (Sum.inr 5137, 1), (Sum.inr 5141, 1), (Sum.inr 5167, 1), (Sum.inr 5168, 1), (Sum.inr 5241, 1), (Sum.inr 5257, 1), (Sum.inr 5258, 1), (Sum.inr 5393, 1), (Sum.inr 5395, 1), (Sum.inr 5405, 1), (Sum.inr 5434, 1), (Sum.inr 5482, 1)]

theorem sourceEq2405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2405 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2405 + difference 0 1) (sourceB2405 + difference 1 0) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2405 + difference 0 1) (sourceB2405 + difference 1 0) sourceC2405) = raw32966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32966; decide +kernel
    rw [ha]
    exact (canonical32966 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2405 + difference 0 2) (sourceB2405 + difference 2 0) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2405 + difference 0 2) (sourceB2405 + difference 2 0) sourceC2405) = raw32967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32967; decide +kernel
    rw [ha]
    exact (canonical32967 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2405 + difference 0 3) (sourceB2405 + difference 3 0) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2405 + difference 0 3) (sourceB2405 + difference 3 0) sourceC2405) = raw32968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32968; decide +kernel
    rw [ha]
    exact (canonical32968 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2405 + difference 0 4) (sourceB2405 + difference 4 0) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA2405 + difference 0 4) (sourceB2405 + difference 4 0) sourceC2405) = raw32969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32969; decide +kernel
    rw [ha]
    exact (canonical32969 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2405 + difference 0 5) (sourceB2405 + difference 5 0) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2405 + difference 0 5) (sourceB2405 + difference 5 0) sourceC2405) = raw32970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32970; decide +kernel
    rw [ha]
    exact (canonical32970 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2405 + difference 1 0) (sourceB2405 + difference 0 1) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA2405 + difference 1 0) (sourceB2405 + difference 0 1) sourceC2405) = raw32971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32971; decide +kernel
    rw [ha]
    exact (canonical32971 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2405 + difference 1 2) (sourceB2405 + difference 2 1) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA2405 + difference 1 2) (sourceB2405 + difference 2 1) sourceC2405) = raw32972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32972; decide +kernel
    rw [ha]
    exact (canonical32972 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2405 + difference 1 3) (sourceB2405 + difference 3 1) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2405 + difference 1 3) (sourceB2405 + difference 3 1) sourceC2405) = raw32973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32973; decide +kernel
    rw [ha]
    exact (canonical32973 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2405 + difference 1 4) (sourceB2405 + difference 4 1) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2405 + difference 1 4) (sourceB2405 + difference 4 1) sourceC2405) = raw32974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32974; decide +kernel
    rw [ha]
    exact (canonical32974 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2405 + difference 1 5) (sourceB2405 + difference 5 1) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2405 + difference 1 5) (sourceB2405 + difference 5 1) sourceC2405) = raw32975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32975; decide +kernel
    rw [ha]
    exact (canonical32975 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2405 + difference 2 0) (sourceB2405 + difference 0 2) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA2405 + difference 2 0) (sourceB2405 + difference 0 2) sourceC2405) = raw32976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32976; decide +kernel
    rw [ha]
    exact (canonical32976 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2405 + difference 2 1) (sourceB2405 + difference 1 2) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2405 + difference 2 1) (sourceB2405 + difference 1 2) sourceC2405) = raw32977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32977; decide +kernel
    rw [ha]
    exact (canonical32977 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2405 + difference 2 3) (sourceB2405 + difference 3 2) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2405 + difference 2 3) (sourceB2405 + difference 3 2) sourceC2405) = raw32978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32978; decide +kernel
    rw [ha]
    exact (canonical32978 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2405 + difference 2 4) (sourceB2405 + difference 4 2) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2405 + difference 2 4) (sourceB2405 + difference 4 2) sourceC2405) = raw32979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32979; decide +kernel
    rw [ha]
    exact (canonical32979 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2405 + difference 2 5) (sourceB2405 + difference 5 2) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2405 + difference 2 5) (sourceB2405 + difference 5 2) sourceC2405) = raw32980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32980; decide +kernel
    rw [ha]
    exact (canonical32980 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2405 + difference 3 0) (sourceB2405 + difference 0 3) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4321) := by
    have ha : (tripleCharges (sourceA2405 + difference 3 0) (sourceB2405 + difference 0 3) sourceC2405) = raw32981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32981; decide +kernel
    rw [ha]
    exact (canonical32981 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2405 + difference 3 1) (sourceB2405 + difference 1 3) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4926) := by
    have ha : (tripleCharges (sourceA2405 + difference 3 1) (sourceB2405 + difference 1 3) sourceC2405) = raw32982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32982; decide +kernel
    rw [ha]
    exact (canonical32982 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2405 + difference 3 2) (sourceB2405 + difference 2 3) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4985) := by
    have ha : (tripleCharges (sourceA2405 + difference 3 2) (sourceB2405 + difference 2 3) sourceC2405) = raw32983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32983; decide +kernel
    rw [ha]
    exact (canonical32983 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2405 + difference 3 4) (sourceB2405 + difference 4 3) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5126) := by
    have ha : (tripleCharges (sourceA2405 + difference 3 4) (sourceB2405 + difference 4 3) sourceC2405) = raw32984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32984; decide +kernel
    rw [ha]
    exact (canonical32984 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2405 + difference 3 5) (sourceB2405 + difference 5 3) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2405 + difference 3 5) (sourceB2405 + difference 5 3) sourceC2405) = raw32985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32985; decide +kernel
    rw [ha]
    exact (canonical32985 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2405 + difference 4 0) (sourceB2405 + difference 0 4) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2405 + difference 4 0) (sourceB2405 + difference 0 4) sourceC2405) = raw32986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32986; decide +kernel
    rw [ha]
    exact (canonical32986 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2405 + difference 4 1) (sourceB2405 + difference 1 4) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2405 + difference 4 1) (sourceB2405 + difference 1 4) sourceC2405) = raw32987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32987; decide +kernel
    rw [ha]
    exact (canonical32987 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2405 + difference 4 2) (sourceB2405 + difference 2 4) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2405 + difference 4 2) (sourceB2405 + difference 2 4) sourceC2405) = raw32988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32988; decide +kernel
    rw [ha]
    exact (canonical32988 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2405 + difference 4 3) (sourceB2405 + difference 3 4) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2405 + difference 4 3) (sourceB2405 + difference 3 4) sourceC2405) = raw32989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32989; decide +kernel
    rw [ha]
    exact (canonical32989 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2405 + difference 4 5) (sourceB2405 + difference 5 4) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2405 + difference 4 5) (sourceB2405 + difference 5 4) sourceC2405) = raw32990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32990; decide +kernel
    rw [ha]
    exact (canonical32990 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2405 + difference 5 0) (sourceB2405 + difference 0 5) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4320) := by
    have ha : (tripleCharges (sourceA2405 + difference 5 0) (sourceB2405 + difference 0 5) sourceC2405) = raw32991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32991; decide +kernel
    rw [ha]
    exact (canonical32991 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2405 + difference 5 1) (sourceB2405 + difference 1 5) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2405 + difference 5 1) (sourceB2405 + difference 1 5) sourceC2405) = raw32992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32992; decide +kernel
    rw [ha]
    exact (canonical32992 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2405 + difference 5 2) (sourceB2405 + difference 2 5) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4709) := by
    have ha : (tripleCharges (sourceA2405 + difference 5 2) (sourceB2405 + difference 2 5) sourceC2405) = raw32993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32993; decide +kernel
    rw [ha]
    exact (canonical32993 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2405 + difference 5 3) (sourceB2405 + difference 3 5) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2405 + difference 5 3) (sourceB2405 + difference 3 5) sourceC2405) = raw32994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32994; decide +kernel
    rw [ha]
    exact (canonical32994 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2405 + difference 5 4) (sourceB2405 + difference 4 5) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2405 + difference 5 4) (sourceB2405 + difference 4 5) sourceC2405) = raw32995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32995; decide +kernel
    rw [ha]
    exact (canonical32995 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2405 sourceB2405 sourceC2405
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2405, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2406 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceB2406 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2406 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2406 : Integer.Sparse Master := [(Sum.inr 4779, 1), (Sum.inr 4782, 1), (Sum.inr 4786, 1), (Sum.inr 4798, 1), (Sum.inr 4834, 1), (Sum.inr 5049, 1), (Sum.inr 5055, 1), (Sum.inr 5056, 1), (Sum.inr 5058, 1), (Sum.inr 5069, 1), (Sum.inr 5073, 1), (Sum.inr 5074, 1), (Sum.inr 5076, 1), (Sum.inr 5086, 1), (Sum.inr 5101, 1), (Sum.inr 5122, 1), (Sum.inr 5123, 1), (Sum.inr 5132, 1), (Sum.inr 5133, 1), (Sum.inr 5134, 1), (Sum.inr 5135, 1), (Sum.inr 5137, 1), (Sum.inr 5149, 1), (Sum.inr 5163, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 1), (Sum.inr 5178, 1), (Sum.inr 5183, 1), (Sum.inr 5184, 1), (Sum.inr 5185, 1)]

theorem sourceEq2406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2406 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2406 + difference 0 1) (sourceB2406 + difference 1 0) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2406 + difference 0 1) (sourceB2406 + difference 1 0) sourceC2406) = raw32996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32996; decide +kernel
    rw [ha]
    exact (canonical32996 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2406 + difference 0 2) (sourceB2406 + difference 2 0) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA2406 + difference 0 2) (sourceB2406 + difference 2 0) sourceC2406) = raw32997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32997; decide +kernel
    rw [ha]
    exact (canonical32997 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2406 + difference 0 3) (sourceB2406 + difference 3 0) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2406 + difference 0 3) (sourceB2406 + difference 3 0) sourceC2406) = raw32998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32998; decide +kernel
    rw [ha]
    exact (canonical32998 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2406 + difference 0 4) (sourceB2406 + difference 4 0) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA2406 + difference 0 4) (sourceB2406 + difference 4 0) sourceC2406) = raw32818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32818; decide +kernel
    rw [ha]
    exact (canonical32818 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2406 + difference 0 5) (sourceB2406 + difference 5 0) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2406 + difference 0 5) (sourceB2406 + difference 5 0) sourceC2406) = raw32901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32901; decide +kernel
    rw [ha]
    exact (canonical32901 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2406 + difference 1 0) (sourceB2406 + difference 0 1) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2406 + difference 1 0) (sourceB2406 + difference 0 1) sourceC2406) = raw32999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32999; decide +kernel
    rw [ha]
    exact (canonical32999 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2406 + difference 1 2) (sourceB2406 + difference 2 1) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5178) := by
    have ha : (tripleCharges (sourceA2406 + difference 1 2) (sourceB2406 + difference 2 1) sourceC2406) = raw33000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw33000; decide +kernel
    rw [ha]
    exact (canonical33000 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2406 + difference 1 3) (sourceB2406 + difference 3 1) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA2406 + difference 1 3) (sourceB2406 + difference 3 1) sourceC2406) = raw33001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw33001; decide +kernel
    rw [ha]
    exact (canonical33001 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2406 + difference 1 4) (sourceB2406 + difference 4 1) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5183) := by
    have ha : (tripleCharges (sourceA2406 + difference 1 4) (sourceB2406 + difference 4 1) sourceC2406) = raw32823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32823; decide +kernel
    rw [ha]
    exact (canonical32823 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2406 + difference 1 5) (sourceB2406 + difference 5 1) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2406 + difference 1 5) (sourceB2406 + difference 5 1) sourceC2406) = raw32905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32905; decide +kernel
    rw [ha]
    exact (canonical32905 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2406 + difference 2 0) (sourceB2406 + difference 0 2) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2406 + difference 2 0) (sourceB2406 + difference 0 2) sourceC2406) = raw32835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32835; decide +kernel
    rw [ha]
    exact (canonical32835 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2406 + difference 2 1) (sourceB2406 + difference 1 2) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2406 + difference 2 1) (sourceB2406 + difference 1 2) sourceC2406) = raw32836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32836; decide +kernel
    rw [ha]
    exact (canonical32836 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2406 + difference 2 3) (sourceB2406 + difference 3 2) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2406 + difference 2 3) (sourceB2406 + difference 3 2) sourceC2406) = raw32335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32335; decide +kernel
    rw [ha]
    exact (canonical32335 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2406 + difference 2 4) (sourceB2406 + difference 4 2) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2406 + difference 2 4) (sourceB2406 + difference 4 2) sourceC2406) = raw33002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw33002; decide +kernel
    rw [ha]
    exact (canonical33002 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2406 + difference 2 5) (sourceB2406 + difference 5 2) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2406 + difference 2 5) (sourceB2406 + difference 5 2) sourceC2406) = raw32254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32254; decide +kernel
    rw [ha]
    exact (canonical32254 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2406 + difference 3 0) (sourceB2406 + difference 0 3) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2406 + difference 3 0) (sourceB2406 + difference 0 3) sourceC2406) = raw33003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw33003; decide +kernel
    rw [ha]
    exact (canonical33003 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2406 + difference 3 1) (sourceB2406 + difference 1 3) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2406 + difference 3 1) (sourceB2406 + difference 1 3) sourceC2406) = raw33004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw33004; decide +kernel
    rw [ha]
    exact (canonical33004 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2406 + difference 3 2) (sourceB2406 + difference 2 3) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5122) := by
    have ha : (tripleCharges (sourceA2406 + difference 3 2) (sourceB2406 + difference 2 3) sourceC2406) = raw33005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw33005; decide +kernel
    rw [ha]
    exact (canonical33005 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2406 + difference 3 4) (sourceB2406 + difference 4 3) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5132) := by
    have ha : (tripleCharges (sourceA2406 + difference 3 4) (sourceB2406 + difference 4 3) sourceC2406) = raw32832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32832; decide +kernel
    rw [ha]
    exact (canonical32832 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2406 + difference 3 5) (sourceB2406 + difference 5 3) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA2406 + difference 3 5) (sourceB2406 + difference 5 3) sourceC2406) = raw32909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32909; decide +kernel
    rw [ha]
    exact (canonical32909 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2406 + difference 4 0) (sourceB2406 + difference 0 4) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4786) := by
    have ha : (tripleCharges (sourceA2406 + difference 4 0) (sourceB2406 + difference 0 4) sourceC2406) = raw32914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32914; decide +kernel
    rw [ha]
    exact (canonical32914 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2406 + difference 4 1) (sourceB2406 + difference 1 4) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5058) := by
    have ha : (tripleCharges (sourceA2406 + difference 4 1) (sourceB2406 + difference 1 4) sourceC2406) = raw32915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32915; decide +kernel
    rw [ha]
    exact (canonical32915 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2406 + difference 4 2) (sourceB2406 + difference 2 4) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2406 + difference 4 2) (sourceB2406 + difference 2 4) sourceC2406) = raw32916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32916; decide +kernel
    rw [ha]
    exact (canonical32916 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2406 + difference 4 3) (sourceB2406 + difference 3 4) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2406 + difference 4 3) (sourceB2406 + difference 3 4) sourceC2406) = raw32917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32917; decide +kernel
    rw [ha]
    exact (canonical32917 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2406 + difference 4 5) (sourceB2406 + difference 5 4) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2406 + difference 4 5) (sourceB2406 + difference 5 4) sourceC2406) = raw32252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32252; decide +kernel
    rw [ha]
    exact (canonical32252 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2406 + difference 5 0) (sourceB2406 + difference 0 5) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2406 + difference 5 0) (sourceB2406 + difference 0 5) sourceC2406) = raw33006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw33006; decide +kernel
    rw [ha]
    exact (canonical33006 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2406 + difference 5 1) (sourceB2406 + difference 1 5) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA2406 + difference 5 1) (sourceB2406 + difference 1 5) sourceC2406) = raw33007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw33007; decide +kernel
    rw [ha]
    exact (canonical33007 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2406 + difference 5 2) (sourceB2406 + difference 2 5) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5049) := by
    have ha : (tripleCharges (sourceA2406 + difference 5 2) (sourceB2406 + difference 2 5) sourceC2406) = raw33008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw33008; decide +kernel
    rw [ha]
    exact (canonical33008 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2406 + difference 5 3) (sourceB2406 + difference 3 5) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5133) := by
    have ha : (tripleCharges (sourceA2406 + difference 5 3) (sourceB2406 + difference 3 5) sourceC2406) = raw33009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw33009; decide +kernel
    rw [ha]
    exact (canonical33009 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2406 + difference 5 4) (sourceB2406 + difference 4 5) sourceC2406) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5069) := by
    have ha : (tripleCharges (sourceA2406 + difference 5 4) (sourceB2406 + difference 4 5) sourceC2406) = raw32840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2406 sourceB2406 sourceC2406 difference raw32840; decide +kernel
    rw [ha]
    exact (canonical32840 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2406 sourceB2406 sourceC2406
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2406, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2407 : Charge := ![1, 1, -2, 0, 0, 0]
def sourceB2407 : Charge := ![2, 0, 2, -1, -1, -2]
def sourceC2407 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2407 : Integer.Sparse Master := [(Sum.inr 1786, 1), (Sum.inr 1787, 2), (Sum.inr 1798, 1), (Sum.inr 1999, 1), (Sum.inr 3370, 1), (Sum.inr 4080, -1)]

theorem sourceEq2407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2407 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2407 + difference 0 0) (sourceB2407 + difference 0 0) sourceC2407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3370) := by
    have ha : (tripleCharges (sourceA2407 + difference 0 0) (sourceB2407 + difference 0 0) sourceC2407) = raw33010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2407 sourceB2407 sourceC2407 difference raw33010; decide +kernel
    rw [ha]
    exact (canonical33010 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2407 + difference 1 0) (sourceB2407 + difference 0 1) sourceC2407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1798) := by
    have ha : (tripleCharges (sourceA2407 + difference 1 0) (sourceB2407 + difference 0 1) sourceC2407) = raw33011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2407 sourceB2407 sourceC2407 difference raw33011; decide +kernel
    rw [ha]
    exact (canonical33011 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2407 + difference 2 0) (sourceB2407 + difference 0 2) sourceC2407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1999) := by
    have ha : (tripleCharges (sourceA2407 + difference 2 0) (sourceB2407 + difference 0 2) sourceC2407) = raw33012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2407 sourceB2407 sourceC2407 difference raw33012; decide +kernel
    rw [ha]
    exact (canonical33012 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2407 + difference 3 0) (sourceB2407 + difference 0 3) sourceC2407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1787) := by
    have ha : (tripleCharges (sourceA2407 + difference 3 0) (sourceB2407 + difference 0 3) sourceC2407) = raw33013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2407 sourceB2407 sourceC2407 difference raw33013; decide +kernel
    rw [ha]
    exact (canonical33013 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2407 + difference 4 0) (sourceB2407 + difference 0 4) sourceC2407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1787) := by
    have ha : (tripleCharges (sourceA2407 + difference 4 0) (sourceB2407 + difference 0 4) sourceC2407) = raw33014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2407 sourceB2407 sourceC2407 difference raw33014; decide +kernel
    rw [ha]
    exact (canonical33014 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2407 + difference 5 0) (sourceB2407 + difference 0 5) sourceC2407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1786) := by
    have ha : (tripleCharges (sourceA2407 + difference 5 0) (sourceB2407 + difference 0 5) sourceC2407) = raw33015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2407 sourceB2407 sourceC2407 difference raw33015; decide +kernel
    rw [ha]
    exact (canonical33015 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2407 + sourceB2407) sourceC2407) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2407 + sourceB2407) sourceC2407) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2407 sourceB2407 sourceC2407 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2407 sourceB2407 sourceC2407
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2407, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2408 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2408 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC2408 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceForm2408 : Integer.Sparse Master := [(Sum.inr 4290, 1), (Sum.inr 4291, 2), (Sum.inr 4307, 1), (Sum.inr 4461, 1), (Sum.inr 4904, 1), (Sum.inr 4905, 2), (Sum.inr 4917, 1), (Sum.inr 5037, 1), (Sum.inr 5038, 2), (Sum.inr 5070, 2), (Sum.inr 5078, 2), (Sum.inr 5080, 2), (Sum.inr 5093, 1), (Sum.inr 5105, 2), (Sum.inr 5172, 1), (Sum.inr 5290, 1), (Sum.inr 5294, 2), (Sum.inr 5354, 1), (Sum.inr 5416, 1), (Sum.inr 5434, 2), (Sum.inr 5481, 1)]

theorem sourceEq2408 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2408 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2408 + difference 0 1) (sourceB2408 + difference 1 0) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2408 + difference 0 1) (sourceB2408 + difference 1 0) sourceC2408) = raw18829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw18829; decide +kernel
    rw [ha]
    exact (canonical18829 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2408 + difference 0 2) (sourceB2408 + difference 2 0) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2408 + difference 0 2) (sourceB2408 + difference 2 0) sourceC2408) = raw18830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw18830; decide +kernel
    rw [ha]
    exact (canonical18830 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2408 + difference 0 3) (sourceB2408 + difference 3 0) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2408 + difference 0 3) (sourceB2408 + difference 3 0) sourceC2408) = raw18831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw18831; decide +kernel
    rw [ha]
    exact (canonical18831 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2408 + difference 0 4) (sourceB2408 + difference 4 0) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2408 + difference 0 4) (sourceB2408 + difference 4 0) sourceC2408) = raw18832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw18832; decide +kernel
    rw [ha]
    exact (canonical18832 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2408 + difference 0 5) (sourceB2408 + difference 5 0) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA2408 + difference 0 5) (sourceB2408 + difference 5 0) sourceC2408) = raw33016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33016; decide +kernel
    rw [ha]
    exact (canonical33016 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2408 + difference 1 0) (sourceB2408 + difference 0 1) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA2408 + difference 1 0) (sourceB2408 + difference 0 1) sourceC2408) = raw33017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33017; decide +kernel
    rw [ha]
    exact (canonical33017 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2408 + difference 1 2) (sourceB2408 + difference 2 1) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2408 + difference 1 2) (sourceB2408 + difference 2 1) sourceC2408) = raw33018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33018; decide +kernel
    rw [ha]
    exact (canonical33018 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2408 + difference 1 3) (sourceB2408 + difference 3 1) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2408 + difference 1 3) (sourceB2408 + difference 3 1) sourceC2408) = raw30312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw30312; decide +kernel
    rw [ha]
    exact (canonical30312 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2408 + difference 1 4) (sourceB2408 + difference 4 1) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2408 + difference 1 4) (sourceB2408 + difference 4 1) sourceC2408) = raw33019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33019; decide +kernel
    rw [ha]
    exact (canonical33019 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2408 + difference 1 5) (sourceB2408 + difference 5 1) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2408 + difference 1 5) (sourceB2408 + difference 5 1) sourceC2408) = raw18808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw18808; decide +kernel
    rw [ha]
    exact (canonical18808 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2408 + difference 2 0) (sourceB2408 + difference 0 2) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4307) := by
    have ha : (tripleCharges (sourceA2408 + difference 2 0) (sourceB2408 + difference 0 2) sourceC2408) = raw33020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33020; decide +kernel
    rw [ha]
    exact (canonical33020 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2408 + difference 2 1) (sourceB2408 + difference 1 2) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4917) := by
    have ha : (tripleCharges (sourceA2408 + difference 2 1) (sourceB2408 + difference 1 2) sourceC2408) = raw33021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33021; decide +kernel
    rw [ha]
    exact (canonical33021 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2408 + difference 2 3) (sourceB2408 + difference 3 2) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2408 + difference 2 3) (sourceB2408 + difference 3 2) sourceC2408) = raw30317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw30317; decide +kernel
    rw [ha]
    exact (canonical30317 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2408 + difference 2 4) (sourceB2408 + difference 4 2) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2408 + difference 2 4) (sourceB2408 + difference 4 2) sourceC2408) = raw33022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33022; decide +kernel
    rw [ha]
    exact (canonical33022 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2408 + difference 2 5) (sourceB2408 + difference 5 2) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5093) := by
    have ha : (tripleCharges (sourceA2408 + difference 2 5) (sourceB2408 + difference 5 2) sourceC2408) = raw18813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw18813; decide +kernel
    rw [ha]
    exact (canonical18813 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2408 + difference 3 0) (sourceB2408 + difference 0 3) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4291) := by
    have ha : (tripleCharges (sourceA2408 + difference 3 0) (sourceB2408 + difference 0 3) sourceC2408) = raw33023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33023; decide +kernel
    rw [ha]
    exact (canonical33023 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2408 + difference 3 1) (sourceB2408 + difference 1 3) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4905) := by
    have ha : (tripleCharges (sourceA2408 + difference 3 1) (sourceB2408 + difference 1 3) sourceC2408) = raw33024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33024; decide +kernel
    rw [ha]
    exact (canonical33024 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2408 + difference 3 2) (sourceB2408 + difference 2 3) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2408 + difference 3 2) (sourceB2408 + difference 2 3) sourceC2408) = raw33025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33025; decide +kernel
    rw [ha]
    exact (canonical33025 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2408 + difference 3 4) (sourceB2408 + difference 4 3) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2408 + difference 3 4) (sourceB2408 + difference 4 3) sourceC2408) = raw33026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33026; decide +kernel
    rw [ha]
    exact (canonical33026 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2408 + difference 3 5) (sourceB2408 + difference 5 3) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2408 + difference 3 5) (sourceB2408 + difference 5 3) sourceC2408) = raw18818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw18818; decide +kernel
    rw [ha]
    exact (canonical18818 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2408 + difference 4 0) (sourceB2408 + difference 0 4) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4291) := by
    have ha : (tripleCharges (sourceA2408 + difference 4 0) (sourceB2408 + difference 0 4) sourceC2408) = raw30319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw30319; decide +kernel
    rw [ha]
    exact (canonical30319 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2408 + difference 4 1) (sourceB2408 + difference 1 4) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4905) := by
    have ha : (tripleCharges (sourceA2408 + difference 4 1) (sourceB2408 + difference 1 4) sourceC2408) = raw30320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw30320; decide +kernel
    rw [ha]
    exact (canonical30320 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2408 + difference 4 2) (sourceB2408 + difference 2 4) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2408 + difference 4 2) (sourceB2408 + difference 2 4) sourceC2408) = raw30321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw30321; decide +kernel
    rw [ha]
    exact (canonical30321 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2408 + difference 4 3) (sourceB2408 + difference 3 4) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2408 + difference 4 3) (sourceB2408 + difference 3 4) sourceC2408) = raw33027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33027; decide +kernel
    rw [ha]
    exact (canonical33027 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2408 + difference 4 5) (sourceB2408 + difference 5 4) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2408 + difference 4 5) (sourceB2408 + difference 5 4) sourceC2408) = raw18823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw18823; decide +kernel
    rw [ha]
    exact (canonical18823 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2408 + difference 5 0) (sourceB2408 + difference 0 5) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4290) := by
    have ha : (tripleCharges (sourceA2408 + difference 5 0) (sourceB2408 + difference 0 5) sourceC2408) = raw33028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33028; decide +kernel
    rw [ha]
    exact (canonical33028 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2408 + difference 5 1) (sourceB2408 + difference 1 5) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4904) := by
    have ha : (tripleCharges (sourceA2408 + difference 5 1) (sourceB2408 + difference 1 5) sourceC2408) = raw33029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33029; decide +kernel
    rw [ha]
    exact (canonical33029 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2408 + difference 5 2) (sourceB2408 + difference 2 5) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5037) := by
    have ha : (tripleCharges (sourceA2408 + difference 5 2) (sourceB2408 + difference 2 5) sourceC2408) = raw33030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33030; decide +kernel
    rw [ha]
    exact (canonical33030 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2408 + difference 5 3) (sourceB2408 + difference 3 5) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2408 + difference 5 3) (sourceB2408 + difference 3 5) sourceC2408) = raw30331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw30331; decide +kernel
    rw [ha]
    exact (canonical30331 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2408 + difference 5 4) (sourceB2408 + difference 4 5) sourceC2408) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2408 + difference 5 4) (sourceB2408 + difference 4 5) sourceC2408) = raw33031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2408 sourceB2408 sourceC2408 difference raw33031; decide +kernel
    rw [ha]
    exact (canonical33031 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2408 sourceB2408 sourceC2408
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2408, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2409 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2409 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC2409 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceForm2409 : Integer.Sparse Master := [(Sum.inr 868, 1), (Sum.inr 869, 2), (Sum.inr 885, 1), (Sum.inr 1044, 1), (Sum.inr 2297, 1), (Sum.inr 2298, 2), (Sum.inr 2308, 1), (Sum.inr 2429, 1), (Sum.inr 2431, 2), (Sum.inr 2477, 2), (Sum.inr 2485, 2), (Sum.inr 2488, 2), (Sum.inr 2503, 1), (Sum.inr 2515, 2), (Sum.inr 2599, 1), (Sum.inr 2764, 1), (Sum.inr 2768, 2), (Sum.inr 3692, 1), (Sum.inr 3967, 1), (Sum.inr 3979, 1), (Sum.inr 3982, 2)]

theorem sourceEq2409 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2409 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2409 + difference 0 1) (sourceB2409 + difference 1 0) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA2409 + difference 0 1) (sourceB2409 + difference 1 0) sourceC2409) = raw18859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw18859; decide +kernel
    rw [ha]
    exact (canonical18859 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2409 + difference 0 2) (sourceB2409 + difference 2 0) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3967) := by
    have ha : (tripleCharges (sourceA2409 + difference 0 2) (sourceB2409 + difference 2 0) sourceC2409) = raw18860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw18860; decide +kernel
    rw [ha]
    exact (canonical18860 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2409 + difference 0 3) (sourceB2409 + difference 3 0) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA2409 + difference 0 3) (sourceB2409 + difference 3 0) sourceC2409) = raw18861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw18861; decide +kernel
    rw [ha]
    exact (canonical18861 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2409 + difference 0 4) (sourceB2409 + difference 4 0) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA2409 + difference 0 4) (sourceB2409 + difference 4 0) sourceC2409) = raw18862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw18862; decide +kernel
    rw [ha]
    exact (canonical18862 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2409 + difference 0 5) (sourceB2409 + difference 5 0) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA2409 + difference 0 5) (sourceB2409 + difference 5 0) sourceC2409) = raw33032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33032; decide +kernel
    rw [ha]
    exact (canonical33032 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2409 + difference 1 0) (sourceB2409 + difference 0 1) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA2409 + difference 1 0) (sourceB2409 + difference 0 1) sourceC2409) = raw33033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33033; decide +kernel
    rw [ha]
    exact (canonical33033 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2409 + difference 1 2) (sourceB2409 + difference 2 1) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA2409 + difference 1 2) (sourceB2409 + difference 2 1) sourceC2409) = raw33034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33034; decide +kernel
    rw [ha]
    exact (canonical33034 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2409 + difference 1 3) (sourceB2409 + difference 3 1) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA2409 + difference 1 3) (sourceB2409 + difference 3 1) sourceC2409) = raw30338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw30338; decide +kernel
    rw [ha]
    exact (canonical30338 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2409 + difference 1 4) (sourceB2409 + difference 4 1) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA2409 + difference 1 4) (sourceB2409 + difference 4 1) sourceC2409) = raw33035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33035; decide +kernel
    rw [ha]
    exact (canonical33035 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2409 + difference 1 5) (sourceB2409 + difference 5 1) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA2409 + difference 1 5) (sourceB2409 + difference 5 1) sourceC2409) = raw18838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw18838; decide +kernel
    rw [ha]
    exact (canonical18838 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2409 + difference 2 0) (sourceB2409 + difference 0 2) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 885) := by
    have ha : (tripleCharges (sourceA2409 + difference 2 0) (sourceB2409 + difference 0 2) sourceC2409) = raw33036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33036; decide +kernel
    rw [ha]
    exact (canonical33036 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2409 + difference 2 1) (sourceB2409 + difference 1 2) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2308) := by
    have ha : (tripleCharges (sourceA2409 + difference 2 1) (sourceB2409 + difference 1 2) sourceC2409) = raw33037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33037; decide +kernel
    rw [ha]
    exact (canonical33037 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2409 + difference 2 3) (sourceB2409 + difference 3 2) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2409 + difference 2 3) (sourceB2409 + difference 3 2) sourceC2409) = raw30343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw30343; decide +kernel
    rw [ha]
    exact (canonical30343 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2409 + difference 2 4) (sourceB2409 + difference 4 2) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2409 + difference 2 4) (sourceB2409 + difference 4 2) sourceC2409) = raw33038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33038; decide +kernel
    rw [ha]
    exact (canonical33038 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2409 + difference 2 5) (sourceB2409 + difference 5 2) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2503) := by
    have ha : (tripleCharges (sourceA2409 + difference 2 5) (sourceB2409 + difference 5 2) sourceC2409) = raw18843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw18843; decide +kernel
    rw [ha]
    exact (canonical18843 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2409 + difference 3 0) (sourceB2409 + difference 0 3) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 869) := by
    have ha : (tripleCharges (sourceA2409 + difference 3 0) (sourceB2409 + difference 0 3) sourceC2409) = raw33039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33039; decide +kernel
    rw [ha]
    exact (canonical33039 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2409 + difference 3 1) (sourceB2409 + difference 1 3) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2298) := by
    have ha : (tripleCharges (sourceA2409 + difference 3 1) (sourceB2409 + difference 1 3) sourceC2409) = raw33040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33040; decide +kernel
    rw [ha]
    exact (canonical33040 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2409 + difference 3 2) (sourceB2409 + difference 2 3) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2409 + difference 3 2) (sourceB2409 + difference 2 3) sourceC2409) = raw33041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33041; decide +kernel
    rw [ha]
    exact (canonical33041 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2409 + difference 3 4) (sourceB2409 + difference 4 3) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2409 + difference 3 4) (sourceB2409 + difference 4 3) sourceC2409) = raw33042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33042; decide +kernel
    rw [ha]
    exact (canonical33042 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2409 + difference 3 5) (sourceB2409 + difference 5 3) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA2409 + difference 3 5) (sourceB2409 + difference 5 3) sourceC2409) = raw18848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw18848; decide +kernel
    rw [ha]
    exact (canonical18848 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2409 + difference 4 0) (sourceB2409 + difference 0 4) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 869) := by
    have ha : (tripleCharges (sourceA2409 + difference 4 0) (sourceB2409 + difference 0 4) sourceC2409) = raw30345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw30345; decide +kernel
    rw [ha]
    exact (canonical30345 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2409 + difference 4 1) (sourceB2409 + difference 1 4) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2298) := by
    have ha : (tripleCharges (sourceA2409 + difference 4 1) (sourceB2409 + difference 1 4) sourceC2409) = raw30346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw30346; decide +kernel
    rw [ha]
    exact (canonical30346 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2409 + difference 4 2) (sourceB2409 + difference 2 4) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2409 + difference 4 2) (sourceB2409 + difference 2 4) sourceC2409) = raw30347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw30347; decide +kernel
    rw [ha]
    exact (canonical30347 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2409 + difference 4 3) (sourceB2409 + difference 3 4) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2409 + difference 4 3) (sourceB2409 + difference 3 4) sourceC2409) = raw33043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33043; decide +kernel
    rw [ha]
    exact (canonical33043 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2409 + difference 4 5) (sourceB2409 + difference 5 4) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA2409 + difference 4 5) (sourceB2409 + difference 5 4) sourceC2409) = raw18853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw18853; decide +kernel
    rw [ha]
    exact (canonical18853 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2409 + difference 5 0) (sourceB2409 + difference 0 5) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 868) := by
    have ha : (tripleCharges (sourceA2409 + difference 5 0) (sourceB2409 + difference 0 5) sourceC2409) = raw33044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33044; decide +kernel
    rw [ha]
    exact (canonical33044 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2409 + difference 5 1) (sourceB2409 + difference 1 5) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2297) := by
    have ha : (tripleCharges (sourceA2409 + difference 5 1) (sourceB2409 + difference 1 5) sourceC2409) = raw33045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33045; decide +kernel
    rw [ha]
    exact (canonical33045 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2409 + difference 5 2) (sourceB2409 + difference 2 5) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA2409 + difference 5 2) (sourceB2409 + difference 2 5) sourceC2409) = raw33046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33046; decide +kernel
    rw [ha]
    exact (canonical33046 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2409 + difference 5 3) (sourceB2409 + difference 3 5) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA2409 + difference 5 3) (sourceB2409 + difference 3 5) sourceC2409) = raw30357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw30357; decide +kernel
    rw [ha]
    exact (canonical30357 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2409 + difference 5 4) (sourceB2409 + difference 4 5) sourceC2409) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA2409 + difference 5 4) (sourceB2409 + difference 4 5) sourceC2409) = raw33047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2409 sourceB2409 sourceC2409 difference raw33047; decide +kernel
    rw [ha]
    exact (canonical33047 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2409 sourceB2409 sourceC2409
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2409, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2410 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2410 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2410 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm2410 : Integer.Sparse Master := [(Sum.inr 4528, 1), (Sum.inr 4530, 1), (Sum.inr 4533, 1), (Sum.inr 4544, 1), (Sum.inr 4590, 1), (Sum.inr 4930, 1), (Sum.inr 4932, 1), (Sum.inr 4933, 1), (Sum.inr 4941, 1), (Sum.inr 5034, 1), (Sum.inr 5043, 1), (Sum.inr 5044, 1), (Sum.inr 5065, 1), (Sum.inr 5067, 1), (Sum.inr 5073, 2), (Sum.inr 5076, 1), (Sum.inr 5078, 1), (Sum.inr 5081, 1), (Sum.inr 5100, 1), (Sum.inr 5104, 1), (Sum.inr 5185, 1), (Sum.inr 5250, 1), (Sum.inr 5257, 1), (Sum.inr 5259, 1), (Sum.inr 5352, 1), (Sum.inr 5401, 1), (Sum.inr 5405, 1), (Sum.inr 5408, 1), (Sum.inr 5410, 1)]

theorem sourceEq2410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2410 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2410 + difference 0 1) (sourceB2410 + difference 1 0) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2410 + difference 0 1) (sourceB2410 + difference 1 0) sourceC2410) = raw33048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33048; decide +kernel
    rw [ha]
    exact (canonical33048 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2410 + difference 0 2) (sourceB2410 + difference 2 0) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2410 + difference 0 2) (sourceB2410 + difference 2 0) sourceC2410) = raw33049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33049; decide +kernel
    rw [ha]
    exact (canonical33049 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2410 + difference 0 3) (sourceB2410 + difference 3 0) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA2410 + difference 0 3) (sourceB2410 + difference 3 0) sourceC2410) = raw7103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw7103; decide +kernel
    rw [ha]
    exact (canonical7103 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2410 + difference 0 4) (sourceB2410 + difference 4 0) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2410 + difference 0 4) (sourceB2410 + difference 4 0) sourceC2410) = raw33050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33050; decide +kernel
    rw [ha]
    exact (canonical33050 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2410 + difference 0 5) (sourceB2410 + difference 5 0) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA2410 + difference 0 5) (sourceB2410 + difference 5 0) sourceC2410) = raw33051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33051; decide +kernel
    rw [ha]
    exact (canonical33051 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2410 + difference 1 0) (sourceB2410 + difference 0 1) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA2410 + difference 1 0) (sourceB2410 + difference 0 1) sourceC2410) = raw7118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw7118; decide +kernel
    rw [ha]
    exact (canonical7118 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2410 + difference 1 2) (sourceB2410 + difference 2 1) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2410 + difference 1 2) (sourceB2410 + difference 2 1) sourceC2410) = raw7120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw7120; decide +kernel
    rw [ha]
    exact (canonical7120 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2410 + difference 1 3) (sourceB2410 + difference 3 1) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA2410 + difference 1 3) (sourceB2410 + difference 3 1) sourceC2410) = raw33052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33052; decide +kernel
    rw [ha]
    exact (canonical33052 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2410 + difference 1 4) (sourceB2410 + difference 4 1) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2410 + difference 1 4) (sourceB2410 + difference 4 1) sourceC2410) = raw7121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw7121; decide +kernel
    rw [ha]
    exact (canonical7121 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2410 + difference 1 5) (sourceB2410 + difference 5 1) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2410 + difference 1 5) (sourceB2410 + difference 5 1) sourceC2410) = raw7122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw7122; decide +kernel
    rw [ha]
    exact (canonical7122 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2410 + difference 2 0) (sourceB2410 + difference 0 2) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA2410 + difference 2 0) (sourceB2410 + difference 0 2) sourceC2410) = raw33053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33053; decide +kernel
    rw [ha]
    exact (canonical33053 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2410 + difference 2 1) (sourceB2410 + difference 1 2) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2410 + difference 2 1) (sourceB2410 + difference 1 2) sourceC2410) = raw33054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33054; decide +kernel
    rw [ha]
    exact (canonical33054 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2410 + difference 2 3) (sourceB2410 + difference 3 2) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2410 + difference 2 3) (sourceB2410 + difference 3 2) sourceC2410) = raw7114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw7114; decide +kernel
    rw [ha]
    exact (canonical7114 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2410 + difference 2 4) (sourceB2410 + difference 4 2) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2410 + difference 2 4) (sourceB2410 + difference 4 2) sourceC2410) = raw33055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33055; decide +kernel
    rw [ha]
    exact (canonical33055 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2410 + difference 2 5) (sourceB2410 + difference 5 2) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5100) := by
    have ha : (tripleCharges (sourceA2410 + difference 2 5) (sourceB2410 + difference 5 2) sourceC2410) = raw33056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33056; decide +kernel
    rw [ha]
    exact (canonical33056 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2410 + difference 3 0) (sourceB2410 + difference 0 3) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4530) := by
    have ha : (tripleCharges (sourceA2410 + difference 3 0) (sourceB2410 + difference 0 3) sourceC2410) = raw33057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33057; decide +kernel
    rw [ha]
    exact (canonical33057 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2410 + difference 3 1) (sourceB2410 + difference 1 3) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4932) := by
    have ha : (tripleCharges (sourceA2410 + difference 3 1) (sourceB2410 + difference 1 3) sourceC2410) = raw33058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33058; decide +kernel
    rw [ha]
    exact (canonical33058 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2410 + difference 3 2) (sourceB2410 + difference 2 3) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5043) := by
    have ha : (tripleCharges (sourceA2410 + difference 3 2) (sourceB2410 + difference 2 3) sourceC2410) = raw33059 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33059; decide +kernel
    rw [ha]
    exact (canonical33059 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2410 + difference 3 4) (sourceB2410 + difference 4 3) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2410 + difference 3 4) (sourceB2410 + difference 4 3) sourceC2410) = raw33060 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33060; decide +kernel
    rw [ha]
    exact (canonical33060 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2410 + difference 3 5) (sourceB2410 + difference 5 3) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2410 + difference 3 5) (sourceB2410 + difference 5 3) sourceC2410) = raw33061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33061; decide +kernel
    rw [ha]
    exact (canonical33061 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2410 + difference 4 0) (sourceB2410 + difference 0 4) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4533) := by
    have ha : (tripleCharges (sourceA2410 + difference 4 0) (sourceB2410 + difference 0 4) sourceC2410) = raw33062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33062; decide +kernel
    rw [ha]
    exact (canonical33062 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2410 + difference 4 1) (sourceB2410 + difference 1 4) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4933) := by
    have ha : (tripleCharges (sourceA2410 + difference 4 1) (sourceB2410 + difference 1 4) sourceC2410) = raw33063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33063; decide +kernel
    rw [ha]
    exact (canonical33063 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2410 + difference 4 2) (sourceB2410 + difference 2 4) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5044) := by
    have ha : (tripleCharges (sourceA2410 + difference 4 2) (sourceB2410 + difference 2 4) sourceC2410) = raw33064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33064; decide +kernel
    rw [ha]
    exact (canonical33064 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2410 + difference 4 3) (sourceB2410 + difference 3 4) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA2410 + difference 4 3) (sourceB2410 + difference 3 4) sourceC2410) = raw7124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw7124; decide +kernel
    rw [ha]
    exact (canonical7124 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2410 + difference 4 5) (sourceB2410 + difference 5 4) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2410 + difference 4 5) (sourceB2410 + difference 5 4) sourceC2410) = raw33065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33065; decide +kernel
    rw [ha]
    exact (canonical33065 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2410 + difference 5 0) (sourceB2410 + difference 0 5) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4528) := by
    have ha : (tripleCharges (sourceA2410 + difference 5 0) (sourceB2410 + difference 0 5) sourceC2410) = raw33066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33066; decide +kernel
    rw [ha]
    exact (canonical33066 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2410 + difference 5 1) (sourceB2410 + difference 1 5) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA2410 + difference 5 1) (sourceB2410 + difference 1 5) sourceC2410) = raw33067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33067; decide +kernel
    rw [ha]
    exact (canonical33067 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2410 + difference 5 2) (sourceB2410 + difference 2 5) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5034) := by
    have ha : (tripleCharges (sourceA2410 + difference 5 2) (sourceB2410 + difference 2 5) sourceC2410) = raw33068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33068; decide +kernel
    rw [ha]
    exact (canonical33068 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2410 + difference 5 3) (sourceB2410 + difference 3 5) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5065) := by
    have ha : (tripleCharges (sourceA2410 + difference 5 3) (sourceB2410 + difference 3 5) sourceC2410) = raw7129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw7129; decide +kernel
    rw [ha]
    exact (canonical7129 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2410 + difference 5 4) (sourceB2410 + difference 4 5) sourceC2410) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2410 + difference 5 4) (sourceB2410 + difference 4 5) sourceC2410) = raw33069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2410 sourceB2410 sourceC2410 difference raw33069; decide +kernel
    rw [ha]
    exact (canonical33069 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2410 sourceB2410 sourceC2410
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2410, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2411 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2411 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2411 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm2411 : Integer.Sparse Master := [(Sum.inr 3260, 1), (Sum.inr 3261, 1), (Sum.inr 3263, 1), (Sum.inr 3267, 1), (Sum.inr 3290, 1), (Sum.inr 3408, 1), (Sum.inr 3409, 1), (Sum.inr 3410, 1), (Sum.inr 3414, 1), (Sum.inr 3451, 1), (Sum.inr 3465, 1), (Sum.inr 3466, 1), (Sum.inr 3467, 2), (Sum.inr 3469, 1), (Sum.inr 3474, 1), (Sum.inr 3476, 1), (Sum.inr 3477, 1), (Sum.inr 3481, 1), (Sum.inr 3482, 1), (Sum.inr 3483, 1), (Sum.inr 3529, 1), (Sum.inr 3531, 1), (Sum.inr 3532, 1), (Sum.inr 3544, 1), (Sum.inr 3764, 1), (Sum.inr 3804, 1), (Sum.inr 3805, 1), (Sum.inr 3806, 1), (Sum.inr 3816, 1)]

theorem sourceEq2411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2411 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2411 + difference 0 1) (sourceB2411 + difference 1 0) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2411 + difference 0 1) (sourceB2411 + difference 1 0) sourceC2411) = raw33070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33070; decide +kernel
    rw [ha]
    exact (canonical33070 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2411 + difference 0 2) (sourceB2411 + difference 2 0) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2411 + difference 0 2) (sourceB2411 + difference 2 0) sourceC2411) = raw33071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33071; decide +kernel
    rw [ha]
    exact (canonical33071 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2411 + difference 0 3) (sourceB2411 + difference 3 0) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA2411 + difference 0 3) (sourceB2411 + difference 3 0) sourceC2411) = raw7163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7163; decide +kernel
    rw [ha]
    exact (canonical7163 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2411 + difference 0 4) (sourceB2411 + difference 4 0) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2411 + difference 0 4) (sourceB2411 + difference 4 0) sourceC2411) = raw33072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33072; decide +kernel
    rw [ha]
    exact (canonical33072 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2411 + difference 0 5) (sourceB2411 + difference 5 0) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA2411 + difference 0 5) (sourceB2411 + difference 5 0) sourceC2411) = raw33073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33073; decide +kernel
    rw [ha]
    exact (canonical33073 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2411 + difference 1 0) (sourceB2411 + difference 0 1) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA2411 + difference 1 0) (sourceB2411 + difference 0 1) sourceC2411) = raw7178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7178; decide +kernel
    rw [ha]
    exact (canonical7178 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2411 + difference 1 2) (sourceB2411 + difference 2 1) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA2411 + difference 1 2) (sourceB2411 + difference 2 1) sourceC2411) = raw7180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7180; decide +kernel
    rw [ha]
    exact (canonical7180 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2411 + difference 1 3) (sourceB2411 + difference 3 1) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA2411 + difference 1 3) (sourceB2411 + difference 3 1) sourceC2411) = raw33074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33074; decide +kernel
    rw [ha]
    exact (canonical33074 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2411 + difference 1 4) (sourceB2411 + difference 4 1) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA2411 + difference 1 4) (sourceB2411 + difference 4 1) sourceC2411) = raw7181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7181; decide +kernel
    rw [ha]
    exact (canonical7181 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2411 + difference 1 5) (sourceB2411 + difference 5 1) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA2411 + difference 1 5) (sourceB2411 + difference 5 1) sourceC2411) = raw7182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7182; decide +kernel
    rw [ha]
    exact (canonical7182 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2411 + difference 2 0) (sourceB2411 + difference 0 2) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3263) := by
    have ha : (tripleCharges (sourceA2411 + difference 2 0) (sourceB2411 + difference 0 2) sourceC2411) = raw33075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33075; decide +kernel
    rw [ha]
    exact (canonical33075 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2411 + difference 2 1) (sourceB2411 + difference 1 2) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3410) := by
    have ha : (tripleCharges (sourceA2411 + difference 2 1) (sourceB2411 + difference 1 2) sourceC2411) = raw33076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33076; decide +kernel
    rw [ha]
    exact (canonical33076 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2411 + difference 2 3) (sourceB2411 + difference 3 2) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA2411 + difference 2 3) (sourceB2411 + difference 3 2) sourceC2411) = raw7174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7174; decide +kernel
    rw [ha]
    exact (canonical7174 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2411 + difference 2 4) (sourceB2411 + difference 4 2) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA2411 + difference 2 4) (sourceB2411 + difference 4 2) sourceC2411) = raw33077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33077; decide +kernel
    rw [ha]
    exact (canonical33077 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2411 + difference 2 5) (sourceB2411 + difference 5 2) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3469) := by
    have ha : (tripleCharges (sourceA2411 + difference 2 5) (sourceB2411 + difference 5 2) sourceC2411) = raw33078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33078; decide +kernel
    rw [ha]
    exact (canonical33078 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2411 + difference 3 0) (sourceB2411 + difference 0 3) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA2411 + difference 3 0) (sourceB2411 + difference 0 3) sourceC2411) = raw33079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33079; decide +kernel
    rw [ha]
    exact (canonical33079 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2411 + difference 3 1) (sourceB2411 + difference 1 3) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3409) := by
    have ha : (tripleCharges (sourceA2411 + difference 3 1) (sourceB2411 + difference 1 3) sourceC2411) = raw33080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33080; decide +kernel
    rw [ha]
    exact (canonical33080 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2411 + difference 3 2) (sourceB2411 + difference 2 3) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3465) := by
    have ha : (tripleCharges (sourceA2411 + difference 3 2) (sourceB2411 + difference 2 3) sourceC2411) = raw33081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33081; decide +kernel
    rw [ha]
    exact (canonical33081 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2411 + difference 3 4) (sourceB2411 + difference 4 3) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2411 + difference 3 4) (sourceB2411 + difference 4 3) sourceC2411) = raw33082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33082; decide +kernel
    rw [ha]
    exact (canonical33082 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2411 + difference 3 5) (sourceB2411 + difference 5 3) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA2411 + difference 3 5) (sourceB2411 + difference 5 3) sourceC2411) = raw33083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33083; decide +kernel
    rw [ha]
    exact (canonical33083 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2411 + difference 4 0) (sourceB2411 + difference 0 4) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA2411 + difference 4 0) (sourceB2411 + difference 0 4) sourceC2411) = raw33084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33084; decide +kernel
    rw [ha]
    exact (canonical33084 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2411 + difference 4 1) (sourceB2411 + difference 1 4) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2411 + difference 4 1) (sourceB2411 + difference 1 4) sourceC2411) = raw33085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33085; decide +kernel
    rw [ha]
    exact (canonical33085 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2411 + difference 4 2) (sourceB2411 + difference 2 4) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2411 + difference 4 2) (sourceB2411 + difference 2 4) sourceC2411) = raw33086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33086; decide +kernel
    rw [ha]
    exact (canonical33086 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2411 + difference 4 3) (sourceB2411 + difference 3 4) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2411 + difference 4 3) (sourceB2411 + difference 3 4) sourceC2411) = raw7184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7184; decide +kernel
    rw [ha]
    exact (canonical7184 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2411 + difference 4 5) (sourceB2411 + difference 5 4) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA2411 + difference 4 5) (sourceB2411 + difference 5 4) sourceC2411) = raw33087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33087; decide +kernel
    rw [ha]
    exact (canonical33087 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2411 + difference 5 0) (sourceB2411 + difference 0 5) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA2411 + difference 5 0) (sourceB2411 + difference 0 5) sourceC2411) = raw33088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33088; decide +kernel
    rw [ha]
    exact (canonical33088 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2411 + difference 5 1) (sourceB2411 + difference 1 5) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2411 + difference 5 1) (sourceB2411 + difference 1 5) sourceC2411) = raw33089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33089; decide +kernel
    rw [ha]
    exact (canonical33089 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2411 + difference 5 2) (sourceB2411 + difference 2 5) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA2411 + difference 5 2) (sourceB2411 + difference 2 5) sourceC2411) = raw33090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33090; decide +kernel
    rw [ha]
    exact (canonical33090 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2411 + difference 5 3) (sourceB2411 + difference 3 5) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA2411 + difference 5 3) (sourceB2411 + difference 3 5) sourceC2411) = raw7189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw7189; decide +kernel
    rw [ha]
    exact (canonical7189 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2411 + difference 5 4) (sourceB2411 + difference 4 5) sourceC2411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2411 + difference 5 4) (sourceB2411 + difference 4 5) sourceC2411) = raw33091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2411 sourceB2411 sourceC2411 difference raw33091; decide +kernel
    rw [ha]
    exact (canonical33091 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2411 sourceB2411 sourceC2411
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2411, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2412 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2412 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2412 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceForm2412 : Integer.Sparse Master := [(Sum.inr 4287, 1), (Sum.inr 4288, 1), (Sum.inr 4292, 1), (Sum.inr 4301, 1), (Sum.inr 4458, 1), (Sum.inr 4902, 1), (Sum.inr 4903, 1), (Sum.inr 4906, 1), (Sum.inr 4912, 1), (Sum.inr 5033, 1), (Sum.inr 5036, 1), (Sum.inr 5039, 1), (Sum.inr 5047, 1), (Sum.inr 5050, 1), (Sum.inr 5059, 1), (Sum.inr 5072, 1), (Sum.inr 5073, 1), (Sum.inr 5075, 1), (Sum.inr 5081, 1), (Sum.inr 5098, 1), (Sum.inr 5102, 1), (Sum.inr 5169, 1), (Sum.inr 5259, 1), (Sum.inr 5292, 1), (Sum.inr 5293, 1), (Sum.inr 5352, 1), (Sum.inr 5476, 1), (Sum.inr 5477, 1), (Sum.inr 5482, 1), (Sum.inr 5483, 1)]

theorem sourceEq2412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2412 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2412 + difference 0 1) (sourceB2412 + difference 1 0) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2412 + difference 0 1) (sourceB2412 + difference 1 0) sourceC2412) = raw33092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33092; decide +kernel
    rw [ha]
    exact (canonical33092 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2412 + difference 0 2) (sourceB2412 + difference 2 0) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA2412 + difference 0 2) (sourceB2412 + difference 2 0) sourceC2412) = raw33093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33093; decide +kernel
    rw [ha]
    exact (canonical33093 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2412 + difference 0 3) (sourceB2412 + difference 3 0) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2412 + difference 0 3) (sourceB2412 + difference 3 0) sourceC2412) = raw30481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw30481; decide +kernel
    rw [ha]
    exact (canonical30481 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2412 + difference 0 4) (sourceB2412 + difference 4 0) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA2412 + difference 0 4) (sourceB2412 + difference 4 0) sourceC2412) = raw33094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33094; decide +kernel
    rw [ha]
    exact (canonical33094 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2412 + difference 0 5) (sourceB2412 + difference 5 0) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2412 + difference 0 5) (sourceB2412 + difference 5 0) sourceC2412) = raw33095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33095; decide +kernel
    rw [ha]
    exact (canonical33095 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2412 + difference 1 0) (sourceB2412 + difference 0 1) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA2412 + difference 1 0) (sourceB2412 + difference 0 1) sourceC2412) = raw27148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw27148; decide +kernel
    rw [ha]
    exact (canonical27148 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2412 + difference 1 2) (sourceB2412 + difference 2 1) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2412 + difference 1 2) (sourceB2412 + difference 2 1) sourceC2412) = raw33096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33096; decide +kernel
    rw [ha]
    exact (canonical33096 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2412 + difference 1 3) (sourceB2412 + difference 3 1) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2412 + difference 1 3) (sourceB2412 + difference 3 1) sourceC2412) = raw30486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw30486; decide +kernel
    rw [ha]
    exact (canonical30486 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2412 + difference 1 4) (sourceB2412 + difference 4 1) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2412 + difference 1 4) (sourceB2412 + difference 4 1) sourceC2412) = raw33097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33097; decide +kernel
    rw [ha]
    exact (canonical33097 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2412 + difference 1 5) (sourceB2412 + difference 5 1) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA2412 + difference 1 5) (sourceB2412 + difference 5 1) sourceC2412) = raw27122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw27122; decide +kernel
    rw [ha]
    exact (canonical27122 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2412 + difference 2 0) (sourceB2412 + difference 0 2) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA2412 + difference 2 0) (sourceB2412 + difference 0 2) sourceC2412) = raw27147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw27147; decide +kernel
    rw [ha]
    exact (canonical27147 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2412 + difference 2 1) (sourceB2412 + difference 1 2) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2412 + difference 2 1) (sourceB2412 + difference 1 2) sourceC2412) = raw33098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33098; decide +kernel
    rw [ha]
    exact (canonical33098 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2412 + difference 2 3) (sourceB2412 + difference 3 2) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2412 + difference 2 3) (sourceB2412 + difference 3 2) sourceC2412) = raw30491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw30491; decide +kernel
    rw [ha]
    exact (canonical30491 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2412 + difference 2 4) (sourceB2412 + difference 4 2) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA2412 + difference 2 4) (sourceB2412 + difference 4 2) sourceC2412) = raw33099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33099; decide +kernel
    rw [ha]
    exact (canonical33099 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2412 + difference 2 5) (sourceB2412 + difference 5 2) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA2412 + difference 2 5) (sourceB2412 + difference 5 2) sourceC2412) = raw27121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw27121; decide +kernel
    rw [ha]
    exact (canonical27121 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2412 + difference 3 0) (sourceB2412 + difference 0 3) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4288) := by
    have ha : (tripleCharges (sourceA2412 + difference 3 0) (sourceB2412 + difference 0 3) sourceC2412) = raw33100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33100; decide +kernel
    rw [ha]
    exact (canonical33100 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2412 + difference 3 1) (sourceB2412 + difference 1 3) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4903) := by
    have ha : (tripleCharges (sourceA2412 + difference 3 1) (sourceB2412 + difference 1 3) sourceC2412) = raw33101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33101; decide +kernel
    rw [ha]
    exact (canonical33101 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2412 + difference 3 2) (sourceB2412 + difference 2 3) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2412 + difference 3 2) (sourceB2412 + difference 2 3) sourceC2412) = raw33102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33102; decide +kernel
    rw [ha]
    exact (canonical33102 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2412 + difference 3 4) (sourceB2412 + difference 4 3) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2412 + difference 3 4) (sourceB2412 + difference 4 3) sourceC2412) = raw33103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33103; decide +kernel
    rw [ha]
    exact (canonical33103 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2412 + difference 3 5) (sourceB2412 + difference 5 3) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2412 + difference 3 5) (sourceB2412 + difference 5 3) sourceC2412) = raw33104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33104; decide +kernel
    rw [ha]
    exact (canonical33104 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2412 + difference 4 0) (sourceB2412 + difference 0 4) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4292) := by
    have ha : (tripleCharges (sourceA2412 + difference 4 0) (sourceB2412 + difference 0 4) sourceC2412) = raw30493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw30493; decide +kernel
    rw [ha]
    exact (canonical30493 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2412 + difference 4 1) (sourceB2412 + difference 1 4) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4906) := by
    have ha : (tripleCharges (sourceA2412 + difference 4 1) (sourceB2412 + difference 1 4) sourceC2412) = raw30494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw30494; decide +kernel
    rw [ha]
    exact (canonical30494 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2412 + difference 4 2) (sourceB2412 + difference 2 4) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5039) := by
    have ha : (tripleCharges (sourceA2412 + difference 4 2) (sourceB2412 + difference 2 4) sourceC2412) = raw30495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw30495; decide +kernel
    rw [ha]
    exact (canonical30495 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2412 + difference 4 3) (sourceB2412 + difference 3 4) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2412 + difference 4 3) (sourceB2412 + difference 3 4) sourceC2412) = raw33105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33105; decide +kernel
    rw [ha]
    exact (canonical33105 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2412 + difference 4 5) (sourceB2412 + difference 5 4) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2412 + difference 4 5) (sourceB2412 + difference 5 4) sourceC2412) = raw30497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw30497; decide +kernel
    rw [ha]
    exact (canonical30497 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2412 + difference 5 0) (sourceB2412 + difference 0 5) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4287) := by
    have ha : (tripleCharges (sourceA2412 + difference 5 0) (sourceB2412 + difference 0 5) sourceC2412) = raw33106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33106; decide +kernel
    rw [ha]
    exact (canonical33106 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2412 + difference 5 1) (sourceB2412 + difference 1 5) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2412 + difference 5 1) (sourceB2412 + difference 1 5) sourceC2412) = raw33107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33107; decide +kernel
    rw [ha]
    exact (canonical33107 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2412 + difference 5 2) (sourceB2412 + difference 2 5) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5033) := by
    have ha : (tripleCharges (sourceA2412 + difference 5 2) (sourceB2412 + difference 2 5) sourceC2412) = raw33108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33108; decide +kernel
    rw [ha]
    exact (canonical33108 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2412 + difference 5 3) (sourceB2412 + difference 3 5) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2412 + difference 5 3) (sourceB2412 + difference 3 5) sourceC2412) = raw30507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw30507; decide +kernel
    rw [ha]
    exact (canonical30507 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2412 + difference 5 4) (sourceB2412 + difference 4 5) sourceC2412) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA2412 + difference 5 4) (sourceB2412 + difference 4 5) sourceC2412) = raw33109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2412 sourceB2412 sourceC2412 difference raw33109; decide +kernel
    rw [ha]
    exact (canonical33109 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2412 sourceB2412 sourceC2412
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2412, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2413 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2413 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2413 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceForm2413 : Integer.Sparse Master := [(Sum.inr 865, 1), (Sum.inr 866, 1), (Sum.inr 870, 1), (Sum.inr 879, 1), (Sum.inr 1041, 1), (Sum.inr 2295, 1), (Sum.inr 2296, 1), (Sum.inr 2299, 1), (Sum.inr 2305, 1), (Sum.inr 2425, 1), (Sum.inr 2428, 1), (Sum.inr 2432, 1), (Sum.inr 2449, 1), (Sum.inr 2452, 1), (Sum.inr 2462, 1), (Sum.inr 2479, 1), (Sum.inr 2480, 1), (Sum.inr 2482, 1), (Sum.inr 2489, 1), (Sum.inr 2508, 1), (Sum.inr 2512, 1), (Sum.inr 2595, 1), (Sum.inr 2723, 1), (Sum.inr 2766, 1), (Sum.inr 2767, 1), (Sum.inr 3690, 1), (Sum.inr 3965, 1), (Sum.inr 3971, 1), (Sum.inr 3980, 1), (Sum.inr 3981, 1)]

theorem sourceEq2413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2413 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2413 + difference 0 1) (sourceB2413 + difference 1 0) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2413 + difference 0 1) (sourceB2413 + difference 1 0) sourceC2413) = raw33110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33110; decide +kernel
    rw [ha]
    exact (canonical33110 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2413 + difference 0 2) (sourceB2413 + difference 2 0) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3965) := by
    have ha : (tripleCharges (sourceA2413 + difference 0 2) (sourceB2413 + difference 2 0) sourceC2413) = raw33111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33111; decide +kernel
    rw [ha]
    exact (canonical33111 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2413 + difference 0 3) (sourceB2413 + difference 3 0) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2413 + difference 0 3) (sourceB2413 + difference 3 0) sourceC2413) = raw30511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw30511; decide +kernel
    rw [ha]
    exact (canonical30511 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2413 + difference 0 4) (sourceB2413 + difference 4 0) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA2413 + difference 0 4) (sourceB2413 + difference 4 0) sourceC2413) = raw33112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33112; decide +kernel
    rw [ha]
    exact (canonical33112 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2413 + difference 0 5) (sourceB2413 + difference 5 0) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA2413 + difference 0 5) (sourceB2413 + difference 5 0) sourceC2413) = raw33113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33113; decide +kernel
    rw [ha]
    exact (canonical33113 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2413 + difference 1 0) (sourceB2413 + difference 0 1) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA2413 + difference 1 0) (sourceB2413 + difference 0 1) sourceC2413) = raw33114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33114; decide +kernel
    rw [ha]
    exact (canonical33114 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2413 + difference 1 2) (sourceB2413 + difference 2 1) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA2413 + difference 1 2) (sourceB2413 + difference 2 1) sourceC2413) = raw33115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33115; decide +kernel
    rw [ha]
    exact (canonical33115 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2413 + difference 1 3) (sourceB2413 + difference 3 1) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA2413 + difference 1 3) (sourceB2413 + difference 3 1) sourceC2413) = raw30516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw30516; decide +kernel
    rw [ha]
    exact (canonical30516 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2413 + difference 1 4) (sourceB2413 + difference 4 1) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2413 + difference 1 4) (sourceB2413 + difference 4 1) sourceC2413) = raw33116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33116; decide +kernel
    rw [ha]
    exact (canonical33116 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2413 + difference 1 5) (sourceB2413 + difference 5 1) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA2413 + difference 1 5) (sourceB2413 + difference 5 1) sourceC2413) = raw33117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33117; decide +kernel
    rw [ha]
    exact (canonical33117 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2413 + difference 2 0) (sourceB2413 + difference 0 2) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 879) := by
    have ha : (tripleCharges (sourceA2413 + difference 2 0) (sourceB2413 + difference 0 2) sourceC2413) = raw33118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33118; decide +kernel
    rw [ha]
    exact (canonical33118 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2413 + difference 2 1) (sourceB2413 + difference 1 2) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2305) := by
    have ha : (tripleCharges (sourceA2413 + difference 2 1) (sourceB2413 + difference 1 2) sourceC2413) = raw33119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33119; decide +kernel
    rw [ha]
    exact (canonical33119 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2413 + difference 2 3) (sourceB2413 + difference 3 2) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2413 + difference 2 3) (sourceB2413 + difference 3 2) sourceC2413) = raw30521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw30521; decide +kernel
    rw [ha]
    exact (canonical30521 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2413 + difference 2 4) (sourceB2413 + difference 4 2) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA2413 + difference 2 4) (sourceB2413 + difference 4 2) sourceC2413) = raw33120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33120; decide +kernel
    rw [ha]
    exact (canonical33120 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2413 + difference 2 5) (sourceB2413 + difference 5 2) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA2413 + difference 2 5) (sourceB2413 + difference 5 2) sourceC2413) = raw33121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33121; decide +kernel
    rw [ha]
    exact (canonical33121 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2413 + difference 3 0) (sourceB2413 + difference 0 3) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA2413 + difference 3 0) (sourceB2413 + difference 0 3) sourceC2413) = raw33122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33122; decide +kernel
    rw [ha]
    exact (canonical33122 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2413 + difference 3 1) (sourceB2413 + difference 1 3) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2296) := by
    have ha : (tripleCharges (sourceA2413 + difference 3 1) (sourceB2413 + difference 1 3) sourceC2413) = raw33123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33123; decide +kernel
    rw [ha]
    exact (canonical33123 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2413 + difference 3 2) (sourceB2413 + difference 2 3) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2428) := by
    have ha : (tripleCharges (sourceA2413 + difference 3 2) (sourceB2413 + difference 2 3) sourceC2413) = raw33124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33124; decide +kernel
    rw [ha]
    exact (canonical33124 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2413 + difference 3 4) (sourceB2413 + difference 4 3) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2413 + difference 3 4) (sourceB2413 + difference 4 3) sourceC2413) = raw33125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33125; decide +kernel
    rw [ha]
    exact (canonical33125 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2413 + difference 3 5) (sourceB2413 + difference 5 3) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA2413 + difference 3 5) (sourceB2413 + difference 5 3) sourceC2413) = raw33126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33126; decide +kernel
    rw [ha]
    exact (canonical33126 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2413 + difference 4 0) (sourceB2413 + difference 0 4) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 870) := by
    have ha : (tripleCharges (sourceA2413 + difference 4 0) (sourceB2413 + difference 0 4) sourceC2413) = raw30523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw30523; decide +kernel
    rw [ha]
    exact (canonical30523 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2413 + difference 4 1) (sourceB2413 + difference 1 4) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2299) := by
    have ha : (tripleCharges (sourceA2413 + difference 4 1) (sourceB2413 + difference 1 4) sourceC2413) = raw30524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw30524; decide +kernel
    rw [ha]
    exact (canonical30524 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2413 + difference 4 2) (sourceB2413 + difference 2 4) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2432) := by
    have ha : (tripleCharges (sourceA2413 + difference 4 2) (sourceB2413 + difference 2 4) sourceC2413) = raw30525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw30525; decide +kernel
    rw [ha]
    exact (canonical30525 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2413 + difference 4 3) (sourceB2413 + difference 3 4) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2413 + difference 4 3) (sourceB2413 + difference 3 4) sourceC2413) = raw33127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33127; decide +kernel
    rw [ha]
    exact (canonical33127 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2413 + difference 4 5) (sourceB2413 + difference 5 4) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA2413 + difference 4 5) (sourceB2413 + difference 5 4) sourceC2413) = raw30527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw30527; decide +kernel
    rw [ha]
    exact (canonical30527 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2413 + difference 5 0) (sourceB2413 + difference 0 5) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 865) := by
    have ha : (tripleCharges (sourceA2413 + difference 5 0) (sourceB2413 + difference 0 5) sourceC2413) = raw33128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33128; decide +kernel
    rw [ha]
    exact (canonical33128 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2413 + difference 5 1) (sourceB2413 + difference 1 5) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2295) := by
    have ha : (tripleCharges (sourceA2413 + difference 5 1) (sourceB2413 + difference 1 5) sourceC2413) = raw33129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33129; decide +kernel
    rw [ha]
    exact (canonical33129 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2413 + difference 5 2) (sourceB2413 + difference 2 5) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2425) := by
    have ha : (tripleCharges (sourceA2413 + difference 5 2) (sourceB2413 + difference 2 5) sourceC2413) = raw33130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33130; decide +kernel
    rw [ha]
    exact (canonical33130 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2413 + difference 5 3) (sourceB2413 + difference 3 5) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2413 + difference 5 3) (sourceB2413 + difference 3 5) sourceC2413) = raw30537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw30537; decide +kernel
    rw [ha]
    exact (canonical30537 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2413 + difference 5 4) (sourceB2413 + difference 4 5) sourceC2413) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA2413 + difference 5 4) (sourceB2413 + difference 4 5) sourceC2413) = raw33131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2413 sourceB2413 sourceC2413 difference raw33131; decide +kernel
    rw [ha]
    exact (canonical33131 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2413 sourceB2413 sourceC2413
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2413, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2414 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceB2414 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2414 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2414 : Integer.Sparse Master := [(Sum.inr 4736, 1), (Sum.inr 4737, 1), (Sum.inr 4739, 1), (Sum.inr 4740, 1), (Sum.inr 4802, 1), (Sum.inr 4996, 1), (Sum.inr 4997, 1), (Sum.inr 4998, 1), (Sum.inr 5005, 1), (Sum.inr 5070, 1), (Sum.inr 5071, 1), (Sum.inr 5072, 1), (Sum.inr 5073, 1), (Sum.inr 5074, 1), (Sum.inr 5076, 1), (Sum.inr 5083, 1), (Sum.inr 5085, 1), (Sum.inr 5086, 1), (Sum.inr 5101, 1), (Sum.inr 5102, 1), (Sum.inr 5104, 1), (Sum.inr 5134, 1), (Sum.inr 5135, 1), (Sum.inr 5137, 1), (Sum.inr 5145, 1), (Sum.inr 5148, 1), (Sum.inr 5149, 1), (Sum.inr 5169, 2), (Sum.inr 5185, 1)]

theorem sourceEq2414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2414 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2414 + difference 0 1) (sourceB2414 + difference 1 0) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2414 + difference 0 1) (sourceB2414 + difference 1 0) sourceC2414) = raw33132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33132; decide +kernel
    rw [ha]
    exact (canonical33132 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2414 + difference 0 2) (sourceB2414 + difference 2 0) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2414 + difference 0 2) (sourceB2414 + difference 2 0) sourceC2414) = raw33133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33133; decide +kernel
    rw [ha]
    exact (canonical33133 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2414 + difference 0 3) (sourceB2414 + difference 3 0) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2414 + difference 0 3) (sourceB2414 + difference 3 0) sourceC2414) = raw32312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32312; decide +kernel
    rw [ha]
    exact (canonical32312 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2414 + difference 0 4) (sourceB2414 + difference 4 0) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA2414 + difference 0 4) (sourceB2414 + difference 4 0) sourceC2414) = raw33134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33134; decide +kernel
    rw [ha]
    exact (canonical33134 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2414 + difference 0 5) (sourceB2414 + difference 5 0) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2414 + difference 0 5) (sourceB2414 + difference 5 0) sourceC2414) = raw33135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33135; decide +kernel
    rw [ha]
    exact (canonical33135 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2414 + difference 1 0) (sourceB2414 + difference 0 1) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2414 + difference 1 0) (sourceB2414 + difference 0 1) sourceC2414) = raw32327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32327; decide +kernel
    rw [ha]
    exact (canonical32327 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2414 + difference 1 2) (sourceB2414 + difference 2 1) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2414 + difference 1 2) (sourceB2414 + difference 2 1) sourceC2414) = raw32254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32254; decide +kernel
    rw [ha]
    exact (canonical32254 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2414 + difference 1 3) (sourceB2414 + difference 3 1) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2414 + difference 1 3) (sourceB2414 + difference 3 1) sourceC2414) = raw32492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32492; decide +kernel
    rw [ha]
    exact (canonical32492 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2414 + difference 1 4) (sourceB2414 + difference 4 1) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA2414 + difference 1 4) (sourceB2414 + difference 4 1) sourceC2414) = raw32329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32329; decide +kernel
    rw [ha]
    exact (canonical32329 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2414 + difference 1 5) (sourceB2414 + difference 5 1) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2414 + difference 1 5) (sourceB2414 + difference 5 1) sourceC2414) = raw32238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32238; decide +kernel
    rw [ha]
    exact (canonical32238 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2414 + difference 2 0) (sourceB2414 + difference 0 2) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2414 + difference 2 0) (sourceB2414 + difference 0 2) sourceC2414) = raw33136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33136; decide +kernel
    rw [ha]
    exact (canonical33136 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2414 + difference 2 1) (sourceB2414 + difference 1 2) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5005) := by
    have ha : (tripleCharges (sourceA2414 + difference 2 1) (sourceB2414 + difference 1 2) sourceC2414) = raw33137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33137; decide +kernel
    rw [ha]
    exact (canonical33137 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2414 + difference 2 3) (sourceB2414 + difference 3 2) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA2414 + difference 2 3) (sourceB2414 + difference 3 2) sourceC2414) = raw32323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32323; decide +kernel
    rw [ha]
    exact (canonical32323 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2414 + difference 2 4) (sourceB2414 + difference 4 2) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5083) := by
    have ha : (tripleCharges (sourceA2414 + difference 2 4) (sourceB2414 + difference 4 2) sourceC2414) = raw33138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33138; decide +kernel
    rw [ha]
    exact (canonical33138 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2414 + difference 2 5) (sourceB2414 + difference 5 2) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA2414 + difference 2 5) (sourceB2414 + difference 5 2) sourceC2414) = raw33139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33139; decide +kernel
    rw [ha]
    exact (canonical33139 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2414 + difference 3 0) (sourceB2414 + difference 0 3) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA2414 + difference 3 0) (sourceB2414 + difference 0 3) sourceC2414) = raw33140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33140; decide +kernel
    rw [ha]
    exact (canonical33140 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2414 + difference 3 1) (sourceB2414 + difference 1 3) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4997) := by
    have ha : (tripleCharges (sourceA2414 + difference 3 1) (sourceB2414 + difference 1 3) sourceC2414) = raw33141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33141; decide +kernel
    rw [ha]
    exact (canonical33141 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2414 + difference 3 2) (sourceB2414 + difference 2 3) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2414 + difference 3 2) (sourceB2414 + difference 2 3) sourceC2414) = raw33142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33142; decide +kernel
    rw [ha]
    exact (canonical33142 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2414 + difference 3 4) (sourceB2414 + difference 4 3) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA2414 + difference 3 4) (sourceB2414 + difference 4 3) sourceC2414) = raw33143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33143; decide +kernel
    rw [ha]
    exact (canonical33143 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2414 + difference 3 5) (sourceB2414 + difference 5 3) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA2414 + difference 3 5) (sourceB2414 + difference 5 3) sourceC2414) = raw33144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33144; decide +kernel
    rw [ha]
    exact (canonical33144 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2414 + difference 4 0) (sourceB2414 + difference 0 4) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4739) := by
    have ha : (tripleCharges (sourceA2414 + difference 4 0) (sourceB2414 + difference 0 4) sourceC2414) = raw33145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33145; decide +kernel
    rw [ha]
    exact (canonical33145 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2414 + difference 4 1) (sourceB2414 + difference 1 4) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA2414 + difference 4 1) (sourceB2414 + difference 1 4) sourceC2414) = raw33146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33146; decide +kernel
    rw [ha]
    exact (canonical33146 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2414 + difference 4 2) (sourceB2414 + difference 2 4) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2414 + difference 4 2) (sourceB2414 + difference 2 4) sourceC2414) = raw32251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32251; decide +kernel
    rw [ha]
    exact (canonical32251 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2414 + difference 4 3) (sourceB2414 + difference 3 4) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2414 + difference 4 3) (sourceB2414 + difference 3 4) sourceC2414) = raw32331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32331; decide +kernel
    rw [ha]
    exact (canonical32331 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2414 + difference 4 5) (sourceB2414 + difference 5 4) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2414 + difference 4 5) (sourceB2414 + difference 5 4) sourceC2414) = raw32236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32236; decide +kernel
    rw [ha]
    exact (canonical32236 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2414 + difference 5 0) (sourceB2414 + difference 0 5) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2414 + difference 5 0) (sourceB2414 + difference 0 5) sourceC2414) = raw33147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33147; decide +kernel
    rw [ha]
    exact (canonical33147 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2414 + difference 5 1) (sourceB2414 + difference 1 5) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA2414 + difference 5 1) (sourceB2414 + difference 1 5) sourceC2414) = raw33148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw33148; decide +kernel
    rw [ha]
    exact (canonical33148 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2414 + difference 5 2) (sourceB2414 + difference 2 5) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2414 + difference 5 2) (sourceB2414 + difference 2 5) sourceC2414) = raw32836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32836; decide +kernel
    rw [ha]
    exact (canonical32836 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2414 + difference 5 3) (sourceB2414 + difference 3 5) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2414 + difference 5 3) (sourceB2414 + difference 3 5) sourceC2414) = raw32334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32334; decide +kernel
    rw [ha]
    exact (canonical32334 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2414 + difference 5 4) (sourceB2414 + difference 4 5) sourceC2414) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2414 + difference 5 4) (sourceB2414 + difference 4 5) sourceC2414) = raw32828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2414 sourceB2414 sourceC2414 difference raw32828; decide +kernel
    rw [ha]
    exact (canonical32828 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2414 sourceB2414 sourceC2414
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2414, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2415 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceB2415 : Charge := ![2, 1, -1, -1, 1, -2]
def sourceC2415 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2415 : Integer.Sparse Master := [(Sum.inr 1875, 1), (Sum.inr 1876, 1), (Sum.inr 1878, 1), (Sum.inr 1908, 1), (Sum.inr 2075, 1), (Sum.inr 3444, 1), (Sum.inr 4080, -1)]

theorem sourceEq2415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2415 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2415 + difference 0 0) (sourceB2415 + difference 0 0) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3444) := by
    have ha : (tripleCharges (sourceA2415 + difference 0 0) (sourceB2415 + difference 0 0) sourceC2415) = raw33149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33149; decide +kernel
    rw [ha]
    exact (canonical33149 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2415 + difference 1 0) (sourceB2415 + difference 0 1) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA2415 + difference 1 0) (sourceB2415 + difference 0 1) sourceC2415) = raw33150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33150; decide +kernel
    rw [ha]
    exact (canonical33150 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2415 + difference 2 0) (sourceB2415 + difference 0 2) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1878) := by
    have ha : (tripleCharges (sourceA2415 + difference 2 0) (sourceB2415 + difference 0 2) sourceC2415) = raw33151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33151; decide +kernel
    rw [ha]
    exact (canonical33151 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2415 + difference 3 0) (sourceB2415 + difference 0 3) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1876) := by
    have ha : (tripleCharges (sourceA2415 + difference 3 0) (sourceB2415 + difference 0 3) sourceC2415) = raw33152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33152; decide +kernel
    rw [ha]
    exact (canonical33152 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2415 + difference 4 0) (sourceB2415 + difference 0 4) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1908) := by
    have ha : (tripleCharges (sourceA2415 + difference 4 0) (sourceB2415 + difference 0 4) sourceC2415) = raw33153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33153; decide +kernel
    rw [ha]
    exact (canonical33153 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2415 + difference 5 0) (sourceB2415 + difference 0 5) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1875) := by
    have ha : (tripleCharges (sourceA2415 + difference 5 0) (sourceB2415 + difference 0 5) sourceC2415) = raw33154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33154; decide +kernel
    rw [ha]
    exact (canonical33154 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2415 + sourceB2415) sourceC2415) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2415 + sourceB2415) sourceC2415) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2415 sourceB2415 sourceC2415 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2415 sourceB2415 sourceC2415
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2415, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2416 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2416 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2416 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm2416 : Integer.Sparse Master := [(Sum.inr 4527, 1), (Sum.inr 4529, 2), (Sum.inr 4541, 1), (Sum.inr 4589, 1), (Sum.inr 4929, 1), (Sum.inr 4931, 2), (Sum.inr 4939, 1), (Sum.inr 5041, 1), (Sum.inr 5042, 2), (Sum.inr 5074, 2), (Sum.inr 5075, 2), (Sum.inr 5080, 2), (Sum.inr 5098, 1), (Sum.inr 5101, 2), (Sum.inr 5184, 1), (Sum.inr 5256, 1), (Sum.inr 5258, 2), (Sum.inr 5351, 1), (Sum.inr 5400, 1), (Sum.inr 5405, 1), (Sum.inr 5409, 2)]

theorem sourceEq2416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2416 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2416 + difference 0 1) (sourceB2416 + difference 1 0) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2416 + difference 0 1) (sourceB2416 + difference 1 0) sourceC2416) = raw33155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33155; decide +kernel
    rw [ha]
    exact (canonical33155 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2416 + difference 0 2) (sourceB2416 + difference 2 0) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA2416 + difference 0 2) (sourceB2416 + difference 2 0) sourceC2416) = raw33156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33156; decide +kernel
    rw [ha]
    exact (canonical33156 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2416 + difference 0 3) (sourceB2416 + difference 3 0) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2416 + difference 0 3) (sourceB2416 + difference 3 0) sourceC2416) = raw33157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33157; decide +kernel
    rw [ha]
    exact (canonical33157 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2416 + difference 0 4) (sourceB2416 + difference 4 0) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2416 + difference 0 4) (sourceB2416 + difference 4 0) sourceC2416) = raw33158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33158; decide +kernel
    rw [ha]
    exact (canonical33158 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2416 + difference 0 5) (sourceB2416 + difference 5 0) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA2416 + difference 0 5) (sourceB2416 + difference 5 0) sourceC2416) = raw11544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11544; decide +kernel
    rw [ha]
    exact (canonical11544 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2416 + difference 1 0) (sourceB2416 + difference 0 1) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA2416 + difference 1 0) (sourceB2416 + difference 0 1) sourceC2416) = raw11569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11569; decide +kernel
    rw [ha]
    exact (canonical11569 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2416 + difference 1 2) (sourceB2416 + difference 2 1) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA2416 + difference 1 2) (sourceB2416 + difference 2 1) sourceC2416) = raw11571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11571; decide +kernel
    rw [ha]
    exact (canonical11571 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2416 + difference 1 3) (sourceB2416 + difference 3 1) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2416 + difference 1 3) (sourceB2416 + difference 3 1) sourceC2416) = raw11572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11572; decide +kernel
    rw [ha]
    exact (canonical11572 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2416 + difference 1 4) (sourceB2416 + difference 4 1) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2416 + difference 1 4) (sourceB2416 + difference 4 1) sourceC2416) = raw11573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11573; decide +kernel
    rw [ha]
    exact (canonical11573 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2416 + difference 1 5) (sourceB2416 + difference 5 1) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA2416 + difference 1 5) (sourceB2416 + difference 5 1) sourceC2416) = raw33159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33159; decide +kernel
    rw [ha]
    exact (canonical33159 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2416 + difference 2 0) (sourceB2416 + difference 0 2) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4541) := by
    have ha : (tripleCharges (sourceA2416 + difference 2 0) (sourceB2416 + difference 0 2) sourceC2416) = raw33160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33160; decide +kernel
    rw [ha]
    exact (canonical33160 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2416 + difference 2 1) (sourceB2416 + difference 1 2) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2416 + difference 2 1) (sourceB2416 + difference 1 2) sourceC2416) = raw33161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33161; decide +kernel
    rw [ha]
    exact (canonical33161 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2416 + difference 2 3) (sourceB2416 + difference 3 2) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2416 + difference 2 3) (sourceB2416 + difference 3 2) sourceC2416) = raw33162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33162; decide +kernel
    rw [ha]
    exact (canonical33162 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2416 + difference 2 4) (sourceB2416 + difference 4 2) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2416 + difference 2 4) (sourceB2416 + difference 4 2) sourceC2416) = raw33163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33163; decide +kernel
    rw [ha]
    exact (canonical33163 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2416 + difference 2 5) (sourceB2416 + difference 5 2) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA2416 + difference 2 5) (sourceB2416 + difference 5 2) sourceC2416) = raw11555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11555; decide +kernel
    rw [ha]
    exact (canonical11555 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2416 + difference 3 0) (sourceB2416 + difference 0 3) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4529) := by
    have ha : (tripleCharges (sourceA2416 + difference 3 0) (sourceB2416 + difference 0 3) sourceC2416) = raw33164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33164; decide +kernel
    rw [ha]
    exact (canonical33164 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2416 + difference 3 1) (sourceB2416 + difference 1 3) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2416 + difference 3 1) (sourceB2416 + difference 1 3) sourceC2416) = raw33165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33165; decide +kernel
    rw [ha]
    exact (canonical33165 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2416 + difference 3 2) (sourceB2416 + difference 2 3) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5042) := by
    have ha : (tripleCharges (sourceA2416 + difference 3 2) (sourceB2416 + difference 2 3) sourceC2416) = raw33166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33166; decide +kernel
    rw [ha]
    exact (canonical33166 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2416 + difference 3 4) (sourceB2416 + difference 4 3) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2416 + difference 3 4) (sourceB2416 + difference 4 3) sourceC2416) = raw33167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33167; decide +kernel
    rw [ha]
    exact (canonical33167 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2416 + difference 3 5) (sourceB2416 + difference 5 3) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA2416 + difference 3 5) (sourceB2416 + difference 5 3) sourceC2416) = raw11560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11560; decide +kernel
    rw [ha]
    exact (canonical11560 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2416 + difference 4 0) (sourceB2416 + difference 0 4) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4529) := by
    have ha : (tripleCharges (sourceA2416 + difference 4 0) (sourceB2416 + difference 0 4) sourceC2416) = raw33168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33168; decide +kernel
    rw [ha]
    exact (canonical33168 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2416 + difference 4 1) (sourceB2416 + difference 1 4) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2416 + difference 4 1) (sourceB2416 + difference 1 4) sourceC2416) = raw33169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33169; decide +kernel
    rw [ha]
    exact (canonical33169 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2416 + difference 4 2) (sourceB2416 + difference 2 4) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5042) := by
    have ha : (tripleCharges (sourceA2416 + difference 4 2) (sourceB2416 + difference 2 4) sourceC2416) = raw33170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33170; decide +kernel
    rw [ha]
    exact (canonical33170 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2416 + difference 4 3) (sourceB2416 + difference 3 4) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2416 + difference 4 3) (sourceB2416 + difference 3 4) sourceC2416) = raw33171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33171; decide +kernel
    rw [ha]
    exact (canonical33171 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2416 + difference 4 5) (sourceB2416 + difference 5 4) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA2416 + difference 4 5) (sourceB2416 + difference 5 4) sourceC2416) = raw11565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11565; decide +kernel
    rw [ha]
    exact (canonical11565 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2416 + difference 5 0) (sourceB2416 + difference 0 5) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4527) := by
    have ha : (tripleCharges (sourceA2416 + difference 5 0) (sourceB2416 + difference 0 5) sourceC2416) = raw33172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33172; decide +kernel
    rw [ha]
    exact (canonical33172 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2416 + difference 5 1) (sourceB2416 + difference 1 5) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4929) := by
    have ha : (tripleCharges (sourceA2416 + difference 5 1) (sourceB2416 + difference 1 5) sourceC2416) = raw33173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33173; decide +kernel
    rw [ha]
    exact (canonical33173 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2416 + difference 5 2) (sourceB2416 + difference 2 5) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5041) := by
    have ha : (tripleCharges (sourceA2416 + difference 5 2) (sourceB2416 + difference 2 5) sourceC2416) = raw33174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33174; decide +kernel
    rw [ha]
    exact (canonical33174 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2416 + difference 5 3) (sourceB2416 + difference 3 5) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2416 + difference 5 3) (sourceB2416 + difference 3 5) sourceC2416) = raw33175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33175; decide +kernel
    rw [ha]
    exact (canonical33175 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2416 + difference 5 4) (sourceB2416 + difference 4 5) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2416 + difference 5 4) (sourceB2416 + difference 4 5) sourceC2416) = raw33176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33176; decide +kernel
    rw [ha]
    exact (canonical33176 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2416 sourceB2416 sourceC2416
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2416, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2417 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2417 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2417 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm2417 : Integer.Sparse Master := [(Sum.inr 3255, 1), (Sum.inr 3256, 1), (Sum.inr 3258, 2), (Sum.inr 3288, 1), (Sum.inr 3403, 1), (Sum.inr 3404, 1), (Sum.inr 3406, 2), (Sum.inr 3458, 1), (Sum.inr 3460, 1), (Sum.inr 3462, 2), (Sum.inr 3463, 2), (Sum.inr 3468, 2), (Sum.inr 3470, 2), (Sum.inr 3478, 2), (Sum.inr 3524, 1), (Sum.inr 3525, 1), (Sum.inr 3533, 2), (Sum.inr 3757, 1), (Sum.inr 3799, 1), (Sum.inr 3800, 1), (Sum.inr 3807, 2)]

theorem sourceEq2417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2417 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2417 + difference 0 1) (sourceB2417 + difference 1 0) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2417 + difference 0 1) (sourceB2417 + difference 1 0) sourceC2417) = raw33177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33177; decide +kernel
    rw [ha]
    exact (canonical33177 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2417 + difference 0 2) (sourceB2417 + difference 2 0) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2417 + difference 0 2) (sourceB2417 + difference 2 0) sourceC2417) = raw33178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33178; decide +kernel
    rw [ha]
    exact (canonical33178 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2417 + difference 0 3) (sourceB2417 + difference 3 0) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2417 + difference 0 3) (sourceB2417 + difference 3 0) sourceC2417) = raw33179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33179; decide +kernel
    rw [ha]
    exact (canonical33179 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2417 + difference 0 4) (sourceB2417 + difference 4 0) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2417 + difference 0 4) (sourceB2417 + difference 4 0) sourceC2417) = raw33180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33180; decide +kernel
    rw [ha]
    exact (canonical33180 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2417 + difference 0 5) (sourceB2417 + difference 5 0) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA2417 + difference 0 5) (sourceB2417 + difference 5 0) sourceC2417) = raw11604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11604; decide +kernel
    rw [ha]
    exact (canonical11604 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2417 + difference 1 0) (sourceB2417 + difference 0 1) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA2417 + difference 1 0) (sourceB2417 + difference 0 1) sourceC2417) = raw11629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11629; decide +kernel
    rw [ha]
    exact (canonical11629 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2417 + difference 1 2) (sourceB2417 + difference 2 1) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA2417 + difference 1 2) (sourceB2417 + difference 2 1) sourceC2417) = raw11631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11631; decide +kernel
    rw [ha]
    exact (canonical11631 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2417 + difference 1 3) (sourceB2417 + difference 3 1) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA2417 + difference 1 3) (sourceB2417 + difference 3 1) sourceC2417) = raw11632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11632; decide +kernel
    rw [ha]
    exact (canonical11632 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2417 + difference 1 4) (sourceB2417 + difference 4 1) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA2417 + difference 1 4) (sourceB2417 + difference 4 1) sourceC2417) = raw11633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11633; decide +kernel
    rw [ha]
    exact (canonical11633 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2417 + difference 1 5) (sourceB2417 + difference 5 1) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA2417 + difference 1 5) (sourceB2417 + difference 5 1) sourceC2417) = raw33181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33181; decide +kernel
    rw [ha]
    exact (canonical33181 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2417 + difference 2 0) (sourceB2417 + difference 0 2) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3256) := by
    have ha : (tripleCharges (sourceA2417 + difference 2 0) (sourceB2417 + difference 0 2) sourceC2417) = raw33182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33182; decide +kernel
    rw [ha]
    exact (canonical33182 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2417 + difference 2 1) (sourceB2417 + difference 1 2) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3404) := by
    have ha : (tripleCharges (sourceA2417 + difference 2 1) (sourceB2417 + difference 1 2) sourceC2417) = raw33183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33183; decide +kernel
    rw [ha]
    exact (canonical33183 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2417 + difference 2 3) (sourceB2417 + difference 3 2) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2417 + difference 2 3) (sourceB2417 + difference 3 2) sourceC2417) = raw33184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33184; decide +kernel
    rw [ha]
    exact (canonical33184 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2417 + difference 2 4) (sourceB2417 + difference 4 2) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2417 + difference 2 4) (sourceB2417 + difference 4 2) sourceC2417) = raw33185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33185; decide +kernel
    rw [ha]
    exact (canonical33185 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2417 + difference 2 5) (sourceB2417 + difference 5 2) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA2417 + difference 2 5) (sourceB2417 + difference 5 2) sourceC2417) = raw11615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11615; decide +kernel
    rw [ha]
    exact (canonical11615 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2417 + difference 3 0) (sourceB2417 + difference 0 3) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA2417 + difference 3 0) (sourceB2417 + difference 0 3) sourceC2417) = raw33186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33186; decide +kernel
    rw [ha]
    exact (canonical33186 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2417 + difference 3 1) (sourceB2417 + difference 1 3) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2417 + difference 3 1) (sourceB2417 + difference 1 3) sourceC2417) = raw33187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33187; decide +kernel
    rw [ha]
    exact (canonical33187 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2417 + difference 3 2) (sourceB2417 + difference 2 3) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3462) := by
    have ha : (tripleCharges (sourceA2417 + difference 3 2) (sourceB2417 + difference 2 3) sourceC2417) = raw33188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33188; decide +kernel
    rw [ha]
    exact (canonical33188 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2417 + difference 3 4) (sourceB2417 + difference 4 3) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2417 + difference 3 4) (sourceB2417 + difference 4 3) sourceC2417) = raw33189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33189; decide +kernel
    rw [ha]
    exact (canonical33189 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2417 + difference 3 5) (sourceB2417 + difference 5 3) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA2417 + difference 3 5) (sourceB2417 + difference 5 3) sourceC2417) = raw11620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11620; decide +kernel
    rw [ha]
    exact (canonical11620 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2417 + difference 4 0) (sourceB2417 + difference 0 4) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA2417 + difference 4 0) (sourceB2417 + difference 0 4) sourceC2417) = raw33190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33190; decide +kernel
    rw [ha]
    exact (canonical33190 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2417 + difference 4 1) (sourceB2417 + difference 1 4) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2417 + difference 4 1) (sourceB2417 + difference 1 4) sourceC2417) = raw33191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33191; decide +kernel
    rw [ha]
    exact (canonical33191 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2417 + difference 4 2) (sourceB2417 + difference 2 4) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3462) := by
    have ha : (tripleCharges (sourceA2417 + difference 4 2) (sourceB2417 + difference 2 4) sourceC2417) = raw33192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33192; decide +kernel
    rw [ha]
    exact (canonical33192 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2417 + difference 4 3) (sourceB2417 + difference 3 4) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2417 + difference 4 3) (sourceB2417 + difference 3 4) sourceC2417) = raw33193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33193; decide +kernel
    rw [ha]
    exact (canonical33193 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2417 + difference 4 5) (sourceB2417 + difference 5 4) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA2417 + difference 4 5) (sourceB2417 + difference 5 4) sourceC2417) = raw11625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11625; decide +kernel
    rw [ha]
    exact (canonical11625 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2417 + difference 5 0) (sourceB2417 + difference 0 5) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3255) := by
    have ha : (tripleCharges (sourceA2417 + difference 5 0) (sourceB2417 + difference 0 5) sourceC2417) = raw33194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33194; decide +kernel
    rw [ha]
    exact (canonical33194 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2417 + difference 5 1) (sourceB2417 + difference 1 5) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3403) := by
    have ha : (tripleCharges (sourceA2417 + difference 5 1) (sourceB2417 + difference 1 5) sourceC2417) = raw33195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33195; decide +kernel
    rw [ha]
    exact (canonical33195 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2417 + difference 5 2) (sourceB2417 + difference 2 5) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3458) := by
    have ha : (tripleCharges (sourceA2417 + difference 5 2) (sourceB2417 + difference 2 5) sourceC2417) = raw33196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33196; decide +kernel
    rw [ha]
    exact (canonical33196 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2417 + difference 5 3) (sourceB2417 + difference 3 5) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2417 + difference 5 3) (sourceB2417 + difference 3 5) sourceC2417) = raw33197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33197; decide +kernel
    rw [ha]
    exact (canonical33197 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2417 + difference 5 4) (sourceB2417 + difference 4 5) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2417 + difference 5 4) (sourceB2417 + difference 4 5) sourceC2417) = raw33198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33198; decide +kernel
    rw [ha]
    exact (canonical33198 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2417 sourceB2417 sourceC2417
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2417, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2418 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2418 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC2418 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceForm2418 : Integer.Sparse Master := [(Sum.inr 4286, 1), (Sum.inr 4288, 2), (Sum.inr 4298, 1), (Sum.inr 4457, 1), (Sum.inr 4755, 1), (Sum.inr 4760, 1), (Sum.inr 4779, 2), (Sum.inr 4903, 2), (Sum.inr 4910, 1), (Sum.inr 5036, 2), (Sum.inr 5050, 2), (Sum.inr 5056, 2), (Sum.inr 5073, 2), (Sum.inr 5098, 1), (Sum.inr 5168, 1), (Sum.inr 5258, 2), (Sum.inr 5292, 1), (Sum.inr 5351, 1), (Sum.inr 5416, 1), (Sum.inr 5424, 2), (Sum.inr 5482, 1)]

theorem sourceEq2418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2418 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2418 + difference 0 1) (sourceB2418 + difference 1 0) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2418 + difference 0 1) (sourceB2418 + difference 1 0) sourceC2418) = raw17594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw17594; decide +kernel
    rw [ha]
    exact (canonical17594 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2418 + difference 0 2) (sourceB2418 + difference 2 0) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2418 + difference 0 2) (sourceB2418 + difference 2 0) sourceC2418) = raw17595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw17595; decide +kernel
    rw [ha]
    exact (canonical17595 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2418 + difference 0 3) (sourceB2418 + difference 3 0) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2418 + difference 0 3) (sourceB2418 + difference 3 0) sourceC2418) = raw18802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw18802; decide +kernel
    rw [ha]
    exact (canonical18802 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2418 + difference 0 4) (sourceB2418 + difference 4 0) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2418 + difference 0 4) (sourceB2418 + difference 4 0) sourceC2418) = raw17596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw17596; decide +kernel
    rw [ha]
    exact (canonical17596 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2418 + difference 0 5) (sourceB2418 + difference 5 0) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2418 + difference 0 5) (sourceB2418 + difference 5 0) sourceC2418) = raw12591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw12591; decide +kernel
    rw [ha]
    exact (canonical12591 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2418 + difference 1 0) (sourceB2418 + difference 0 1) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA2418 + difference 1 0) (sourceB2418 + difference 0 1) sourceC2418) = raw12616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw12616; decide +kernel
    rw [ha]
    exact (canonical12616 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2418 + difference 1 2) (sourceB2418 + difference 2 1) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2418 + difference 1 2) (sourceB2418 + difference 2 1) sourceC2418) = raw12618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw12618; decide +kernel
    rw [ha]
    exact (canonical12618 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2418 + difference 1 3) (sourceB2418 + difference 3 1) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2418 + difference 1 3) (sourceB2418 + difference 3 1) sourceC2418) = raw12619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw12619; decide +kernel
    rw [ha]
    exact (canonical12619 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2418 + difference 1 4) (sourceB2418 + difference 4 1) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2418 + difference 1 4) (sourceB2418 + difference 4 1) sourceC2418) = raw12620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw12620; decide +kernel
    rw [ha]
    exact (canonical12620 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2418 + difference 1 5) (sourceB2418 + difference 5 1) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA2418 + difference 1 5) (sourceB2418 + difference 5 1) sourceC2418) = raw18791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw18791; decide +kernel
    rw [ha]
    exact (canonical18791 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2418 + difference 2 0) (sourceB2418 + difference 0 2) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4298) := by
    have ha : (tripleCharges (sourceA2418 + difference 2 0) (sourceB2418 + difference 0 2) sourceC2418) = raw33199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33199; decide +kernel
    rw [ha]
    exact (canonical33199 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2418 + difference 2 1) (sourceB2418 + difference 1 2) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4910) := by
    have ha : (tripleCharges (sourceA2418 + difference 2 1) (sourceB2418 + difference 1 2) sourceC2418) = raw33200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33200; decide +kernel
    rw [ha]
    exact (canonical33200 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2418 + difference 2 3) (sourceB2418 + difference 3 2) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2418 + difference 2 3) (sourceB2418 + difference 3 2) sourceC2418) = raw17589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw17589; decide +kernel
    rw [ha]
    exact (canonical17589 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2418 + difference 2 4) (sourceB2418 + difference 4 2) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2418 + difference 2 4) (sourceB2418 + difference 4 2) sourceC2418) = raw33201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33201; decide +kernel
    rw [ha]
    exact (canonical33201 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2418 + difference 2 5) (sourceB2418 + difference 5 2) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA2418 + difference 2 5) (sourceB2418 + difference 5 2) sourceC2418) = raw12602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw12602; decide +kernel
    rw [ha]
    exact (canonical12602 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2418 + difference 3 0) (sourceB2418 + difference 0 3) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4288) := by
    have ha : (tripleCharges (sourceA2418 + difference 3 0) (sourceB2418 + difference 0 3) sourceC2418) = raw33202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33202; decide +kernel
    rw [ha]
    exact (canonical33202 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2418 + difference 3 1) (sourceB2418 + difference 1 3) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4903) := by
    have ha : (tripleCharges (sourceA2418 + difference 3 1) (sourceB2418 + difference 1 3) sourceC2418) = raw33203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33203; decide +kernel
    rw [ha]
    exact (canonical33203 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2418 + difference 3 2) (sourceB2418 + difference 2 3) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2418 + difference 3 2) (sourceB2418 + difference 2 3) sourceC2418) = raw33204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33204; decide +kernel
    rw [ha]
    exact (canonical33204 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2418 + difference 3 4) (sourceB2418 + difference 4 3) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2418 + difference 3 4) (sourceB2418 + difference 4 3) sourceC2418) = raw33205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33205; decide +kernel
    rw [ha]
    exact (canonical33205 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2418 + difference 3 5) (sourceB2418 + difference 5 3) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2418 + difference 3 5) (sourceB2418 + difference 5 3) sourceC2418) = raw12607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw12607; decide +kernel
    rw [ha]
    exact (canonical12607 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2418 + difference 4 0) (sourceB2418 + difference 0 4) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4288) := by
    have ha : (tripleCharges (sourceA2418 + difference 4 0) (sourceB2418 + difference 0 4) sourceC2418) = raw33206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33206; decide +kernel
    rw [ha]
    exact (canonical33206 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2418 + difference 4 1) (sourceB2418 + difference 1 4) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4903) := by
    have ha : (tripleCharges (sourceA2418 + difference 4 1) (sourceB2418 + difference 1 4) sourceC2418) = raw33207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33207; decide +kernel
    rw [ha]
    exact (canonical33207 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2418 + difference 4 2) (sourceB2418 + difference 2 4) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2418 + difference 4 2) (sourceB2418 + difference 2 4) sourceC2418) = raw33208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33208; decide +kernel
    rw [ha]
    exact (canonical33208 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2418 + difference 4 3) (sourceB2418 + difference 3 4) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2418 + difference 4 3) (sourceB2418 + difference 3 4) sourceC2418) = raw17597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw17597; decide +kernel
    rw [ha]
    exact (canonical17597 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2418 + difference 4 5) (sourceB2418 + difference 5 4) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2418 + difference 4 5) (sourceB2418 + difference 5 4) sourceC2418) = raw12612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw12612; decide +kernel
    rw [ha]
    exact (canonical12612 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2418 + difference 5 0) (sourceB2418 + difference 0 5) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4286) := by
    have ha : (tripleCharges (sourceA2418 + difference 5 0) (sourceB2418 + difference 0 5) sourceC2418) = raw33209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33209; decide +kernel
    rw [ha]
    exact (canonical33209 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2418 + difference 5 1) (sourceB2418 + difference 1 5) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4755) := by
    have ha : (tripleCharges (sourceA2418 + difference 5 1) (sourceB2418 + difference 1 5) sourceC2418) = raw33210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33210; decide +kernel
    rw [ha]
    exact (canonical33210 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2418 + difference 5 2) (sourceB2418 + difference 2 5) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2418 + difference 5 2) (sourceB2418 + difference 2 5) sourceC2418) = raw33211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33211; decide +kernel
    rw [ha]
    exact (canonical33211 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2418 + difference 5 3) (sourceB2418 + difference 3 5) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2418 + difference 5 3) (sourceB2418 + difference 3 5) sourceC2418) = raw17602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw17602; decide +kernel
    rw [ha]
    exact (canonical17602 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2418 + difference 5 4) (sourceB2418 + difference 4 5) sourceC2418) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2418 + difference 5 4) (sourceB2418 + difference 4 5) sourceC2418) = raw33212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2418 sourceB2418 sourceC2418 difference raw33212; decide +kernel
    rw [ha]
    exact (canonical33212 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2418 sourceB2418 sourceC2418
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2418, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2419 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2419 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC2419 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceForm2419 : Integer.Sparse Master := [(Sum.inr 864, 1), (Sum.inr 866, 2), (Sum.inr 876, 1), (Sum.inr 1040, 1), (Sum.inr 1954, 1), (Sum.inr 1960, 1), (Sum.inr 1987, 2), (Sum.inr 2296, 2), (Sum.inr 2303, 1), (Sum.inr 2428, 2), (Sum.inr 2452, 2), (Sum.inr 2459, 2), (Sum.inr 2480, 2), (Sum.inr 2508, 1), (Sum.inr 2594, 1), (Sum.inr 2722, 2), (Sum.inr 2766, 1), (Sum.inr 3689, 1), (Sum.inr 3821, 1), (Sum.inr 3838, 2), (Sum.inr 3980, 1)]

theorem sourceEq2419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2419 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2419 + difference 0 1) (sourceB2419 + difference 1 0) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3689) := by
    have ha : (tripleCharges (sourceA2419 + difference 0 1) (sourceB2419 + difference 1 0) sourceC2419) = raw17620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw17620; decide +kernel
    rw [ha]
    exact (canonical17620 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2419 + difference 0 2) (sourceB2419 + difference 2 0) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3821) := by
    have ha : (tripleCharges (sourceA2419 + difference 0 2) (sourceB2419 + difference 2 0) sourceC2419) = raw17621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw17621; decide +kernel
    rw [ha]
    exact (canonical17621 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2419 + difference 0 3) (sourceB2419 + difference 3 0) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA2419 + difference 0 3) (sourceB2419 + difference 3 0) sourceC2419) = raw33213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33213; decide +kernel
    rw [ha]
    exact (canonical33213 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2419 + difference 0 4) (sourceB2419 + difference 4 0) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA2419 + difference 0 4) (sourceB2419 + difference 4 0) sourceC2419) = raw17622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw17622; decide +kernel
    rw [ha]
    exact (canonical17622 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2419 + difference 0 5) (sourceB2419 + difference 5 0) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA2419 + difference 0 5) (sourceB2419 + difference 5 0) sourceC2419) = raw12621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw12621; decide +kernel
    rw [ha]
    exact (canonical12621 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2419 + difference 1 0) (sourceB2419 + difference 0 1) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA2419 + difference 1 0) (sourceB2419 + difference 0 1) sourceC2419) = raw12646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw12646; decide +kernel
    rw [ha]
    exact (canonical12646 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2419 + difference 1 2) (sourceB2419 + difference 2 1) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2594) := by
    have ha : (tripleCharges (sourceA2419 + difference 1 2) (sourceB2419 + difference 2 1) sourceC2419) = raw12648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw12648; decide +kernel
    rw [ha]
    exact (canonical12648 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2419 + difference 1 3) (sourceB2419 + difference 3 1) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2419 + difference 1 3) (sourceB2419 + difference 3 1) sourceC2419) = raw12649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw12649; decide +kernel
    rw [ha]
    exact (canonical12649 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2419 + difference 1 4) (sourceB2419 + difference 4 1) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2419 + difference 1 4) (sourceB2419 + difference 4 1) sourceC2419) = raw12650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw12650; decide +kernel
    rw [ha]
    exact (canonical12650 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2419 + difference 1 5) (sourceB2419 + difference 5 1) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA2419 + difference 1 5) (sourceB2419 + difference 5 1) sourceC2419) = raw33214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33214; decide +kernel
    rw [ha]
    exact (canonical33214 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2419 + difference 2 0) (sourceB2419 + difference 0 2) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 876) := by
    have ha : (tripleCharges (sourceA2419 + difference 2 0) (sourceB2419 + difference 0 2) sourceC2419) = raw33215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33215; decide +kernel
    rw [ha]
    exact (canonical33215 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2419 + difference 2 1) (sourceB2419 + difference 1 2) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2303) := by
    have ha : (tripleCharges (sourceA2419 + difference 2 1) (sourceB2419 + difference 1 2) sourceC2419) = raw33216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33216; decide +kernel
    rw [ha]
    exact (canonical33216 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2419 + difference 2 3) (sourceB2419 + difference 3 2) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA2419 + difference 2 3) (sourceB2419 + difference 3 2) sourceC2419) = raw17615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw17615; decide +kernel
    rw [ha]
    exact (canonical17615 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2419 + difference 2 4) (sourceB2419 + difference 4 2) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA2419 + difference 2 4) (sourceB2419 + difference 4 2) sourceC2419) = raw33217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33217; decide +kernel
    rw [ha]
    exact (canonical33217 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2419 + difference 2 5) (sourceB2419 + difference 5 2) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA2419 + difference 2 5) (sourceB2419 + difference 5 2) sourceC2419) = raw12632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw12632; decide +kernel
    rw [ha]
    exact (canonical12632 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2419 + difference 3 0) (sourceB2419 + difference 0 3) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA2419 + difference 3 0) (sourceB2419 + difference 0 3) sourceC2419) = raw33218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33218; decide +kernel
    rw [ha]
    exact (canonical33218 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2419 + difference 3 1) (sourceB2419 + difference 1 3) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2296) := by
    have ha : (tripleCharges (sourceA2419 + difference 3 1) (sourceB2419 + difference 1 3) sourceC2419) = raw33219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33219; decide +kernel
    rw [ha]
    exact (canonical33219 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2419 + difference 3 2) (sourceB2419 + difference 2 3) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2428) := by
    have ha : (tripleCharges (sourceA2419 + difference 3 2) (sourceB2419 + difference 2 3) sourceC2419) = raw33220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33220; decide +kernel
    rw [ha]
    exact (canonical33220 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2419 + difference 3 4) (sourceB2419 + difference 4 3) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2419 + difference 3 4) (sourceB2419 + difference 4 3) sourceC2419) = raw33221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33221; decide +kernel
    rw [ha]
    exact (canonical33221 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2419 + difference 3 5) (sourceB2419 + difference 5 3) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA2419 + difference 3 5) (sourceB2419 + difference 5 3) sourceC2419) = raw12637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw12637; decide +kernel
    rw [ha]
    exact (canonical12637 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2419 + difference 4 0) (sourceB2419 + difference 0 4) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA2419 + difference 4 0) (sourceB2419 + difference 0 4) sourceC2419) = raw33222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33222; decide +kernel
    rw [ha]
    exact (canonical33222 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2419 + difference 4 1) (sourceB2419 + difference 1 4) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2296) := by
    have ha : (tripleCharges (sourceA2419 + difference 4 1) (sourceB2419 + difference 1 4) sourceC2419) = raw33223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33223; decide +kernel
    rw [ha]
    exact (canonical33223 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2419 + difference 4 2) (sourceB2419 + difference 2 4) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2428) := by
    have ha : (tripleCharges (sourceA2419 + difference 4 2) (sourceB2419 + difference 2 4) sourceC2419) = raw33224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33224; decide +kernel
    rw [ha]
    exact (canonical33224 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2419 + difference 4 3) (sourceB2419 + difference 3 4) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2419 + difference 4 3) (sourceB2419 + difference 3 4) sourceC2419) = raw17623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw17623; decide +kernel
    rw [ha]
    exact (canonical17623 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2419 + difference 4 5) (sourceB2419 + difference 5 4) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA2419 + difference 4 5) (sourceB2419 + difference 5 4) sourceC2419) = raw12642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw12642; decide +kernel
    rw [ha]
    exact (canonical12642 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2419 + difference 5 0) (sourceB2419 + difference 0 5) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 864) := by
    have ha : (tripleCharges (sourceA2419 + difference 5 0) (sourceB2419 + difference 0 5) sourceC2419) = raw33225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33225; decide +kernel
    rw [ha]
    exact (canonical33225 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2419 + difference 5 1) (sourceB2419 + difference 1 5) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1954) := by
    have ha : (tripleCharges (sourceA2419 + difference 5 1) (sourceB2419 + difference 1 5) sourceC2419) = raw33226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33226; decide +kernel
    rw [ha]
    exact (canonical33226 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2419 + difference 5 2) (sourceB2419 + difference 2 5) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1960) := by
    have ha : (tripleCharges (sourceA2419 + difference 5 2) (sourceB2419 + difference 2 5) sourceC2419) = raw33227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33227; decide +kernel
    rw [ha]
    exact (canonical33227 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2419 + difference 5 3) (sourceB2419 + difference 3 5) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA2419 + difference 5 3) (sourceB2419 + difference 3 5) sourceC2419) = raw17628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw17628; decide +kernel
    rw [ha]
    exact (canonical17628 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2419 + difference 5 4) (sourceB2419 + difference 4 5) sourceC2419) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA2419 + difference 5 4) (sourceB2419 + difference 4 5) sourceC2419) = raw33228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2419 sourceB2419 sourceC2419 difference raw33228; decide +kernel
    rw [ha]
    exact (canonical33228 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2419 sourceB2419 sourceC2419
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2419, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2420 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB2420 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC2420 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2420 : Integer.Sparse Master := [(Sum.inr 4728, 1), (Sum.inr 4731, 1), (Sum.inr 4736, 2), (Sum.inr 4801, 1), (Sum.inr 4995, 1), (Sum.inr 4996, 2), (Sum.inr 5004, 1), (Sum.inr 5069, 2), (Sum.inr 5070, 2), (Sum.inr 5073, 2), (Sum.inr 5082, 2), (Sum.inr 5085, 1), (Sum.inr 5099, 1), (Sum.inr 5101, 2), (Sum.inr 5137, 1), (Sum.inr 5138, 2), (Sum.inr 5144, 2), (Sum.inr 5148, 1), (Sum.inr 5168, 1), (Sum.inr 5172, 1), (Sum.inr 5187, 1)]

theorem sourceEq2420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2420 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2420 + difference 0 1) (sourceB2420 + difference 1 0) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA2420 + difference 0 1) (sourceB2420 + difference 1 0) sourceC2420) = raw33229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33229; decide +kernel
    rw [ha]
    exact (canonical33229 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2420 + difference 0 2) (sourceB2420 + difference 2 0) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2420 + difference 0 2) (sourceB2420 + difference 2 0) sourceC2420) = raw33230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33230; decide +kernel
    rw [ha]
    exact (canonical33230 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2420 + difference 0 3) (sourceB2420 + difference 3 0) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2420 + difference 0 3) (sourceB2420 + difference 3 0) sourceC2420) = raw33231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33231; decide +kernel
    rw [ha]
    exact (canonical33231 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2420 + difference 0 4) (sourceB2420 + difference 4 0) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2420 + difference 0 4) (sourceB2420 + difference 4 0) sourceC2420) = raw33232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33232; decide +kernel
    rw [ha]
    exact (canonical33232 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2420 + difference 0 5) (sourceB2420 + difference 5 0) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2420 + difference 0 5) (sourceB2420 + difference 5 0) sourceC2420) = raw32312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw32312; decide +kernel
    rw [ha]
    exact (canonical32312 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2420 + difference 1 0) (sourceB2420 + difference 0 1) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2420 + difference 1 0) (sourceB2420 + difference 0 1) sourceC2420) = raw32333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw32333; decide +kernel
    rw [ha]
    exact (canonical32333 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2420 + difference 1 2) (sourceB2420 + difference 2 1) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2420 + difference 1 2) (sourceB2420 + difference 2 1) sourceC2420) = raw32335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw32335; decide +kernel
    rw [ha]
    exact (canonical32335 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2420 + difference 1 3) (sourceB2420 + difference 3 1) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA2420 + difference 1 3) (sourceB2420 + difference 3 1) sourceC2420) = raw32336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw32336; decide +kernel
    rw [ha]
    exact (canonical32336 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2420 + difference 1 4) (sourceB2420 + difference 4 1) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA2420 + difference 1 4) (sourceB2420 + difference 4 1) sourceC2420) = raw32337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw32337; decide +kernel
    rw [ha]
    exact (canonical32337 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2420 + difference 1 5) (sourceB2420 + difference 5 1) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2420 + difference 1 5) (sourceB2420 + difference 5 1) sourceC2420) = raw32492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw32492; decide +kernel
    rw [ha]
    exact (canonical32492 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2420 + difference 2 0) (sourceB2420 + difference 0 2) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA2420 + difference 2 0) (sourceB2420 + difference 0 2) sourceC2420) = raw33233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33233; decide +kernel
    rw [ha]
    exact (canonical33233 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2420 + difference 2 1) (sourceB2420 + difference 1 2) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5004) := by
    have ha : (tripleCharges (sourceA2420 + difference 2 1) (sourceB2420 + difference 1 2) sourceC2420) = raw33234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33234; decide +kernel
    rw [ha]
    exact (canonical33234 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2420 + difference 2 3) (sourceB2420 + difference 3 2) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5082) := by
    have ha : (tripleCharges (sourceA2420 + difference 2 3) (sourceB2420 + difference 3 2) sourceC2420) = raw33235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33235; decide +kernel
    rw [ha]
    exact (canonical33235 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2420 + difference 2 4) (sourceB2420 + difference 4 2) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5082) := by
    have ha : (tripleCharges (sourceA2420 + difference 2 4) (sourceB2420 + difference 4 2) sourceC2420) = raw33236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33236; decide +kernel
    rw [ha]
    exact (canonical33236 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2420 + difference 2 5) (sourceB2420 + difference 5 2) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA2420 + difference 2 5) (sourceB2420 + difference 5 2) sourceC2420) = raw32323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw32323; decide +kernel
    rw [ha]
    exact (canonical32323 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2420 + difference 3 0) (sourceB2420 + difference 0 3) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2420 + difference 3 0) (sourceB2420 + difference 0 3) sourceC2420) = raw33147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33147; decide +kernel
    rw [ha]
    exact (canonical33147 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2420 + difference 3 1) (sourceB2420 + difference 1 3) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA2420 + difference 3 1) (sourceB2420 + difference 1 3) sourceC2420) = raw33148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33148; decide +kernel
    rw [ha]
    exact (canonical33148 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2420 + difference 3 2) (sourceB2420 + difference 2 3) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2420 + difference 3 2) (sourceB2420 + difference 2 3) sourceC2420) = raw32836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw32836; decide +kernel
    rw [ha]
    exact (canonical32836 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2420 + difference 3 4) (sourceB2420 + difference 4 3) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2420 + difference 3 4) (sourceB2420 + difference 4 3) sourceC2420) = raw32828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw32828; decide +kernel
    rw [ha]
    exact (canonical32828 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2420 + difference 3 5) (sourceB2420 + difference 5 3) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2420 + difference 3 5) (sourceB2420 + difference 5 3) sourceC2420) = raw32328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw32328; decide +kernel
    rw [ha]
    exact (canonical32328 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2420 + difference 4 0) (sourceB2420 + difference 0 4) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2420 + difference 4 0) (sourceB2420 + difference 0 4) sourceC2420) = raw33237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33237; decide +kernel
    rw [ha]
    exact (canonical33237 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2420 + difference 4 1) (sourceB2420 + difference 1 4) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA2420 + difference 4 1) (sourceB2420 + difference 1 4) sourceC2420) = raw33238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33238; decide +kernel
    rw [ha]
    exact (canonical33238 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2420 + difference 4 2) (sourceB2420 + difference 2 4) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2420 + difference 4 2) (sourceB2420 + difference 2 4) sourceC2420) = raw33239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33239; decide +kernel
    rw [ha]
    exact (canonical33239 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2420 + difference 4 3) (sourceB2420 + difference 3 4) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2420 + difference 4 3) (sourceB2420 + difference 3 4) sourceC2420) = raw33240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33240; decide +kernel
    rw [ha]
    exact (canonical33240 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2420 + difference 4 5) (sourceB2420 + difference 5 4) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2420 + difference 4 5) (sourceB2420 + difference 5 4) sourceC2420) = raw32331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw32331; decide +kernel
    rw [ha]
    exact (canonical32331 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2420 + difference 5 0) (sourceB2420 + difference 0 5) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2420 + difference 5 0) (sourceB2420 + difference 0 5) sourceC2420) = raw33241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33241; decide +kernel
    rw [ha]
    exact (canonical33241 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2420 + difference 5 1) (sourceB2420 + difference 1 5) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4995) := by
    have ha : (tripleCharges (sourceA2420 + difference 5 1) (sourceB2420 + difference 1 5) sourceC2420) = raw33242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33242; decide +kernel
    rw [ha]
    exact (canonical33242 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2420 + difference 5 2) (sourceB2420 + difference 2 5) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2420 + difference 5 2) (sourceB2420 + difference 2 5) sourceC2420) = raw33243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33243; decide +kernel
    rw [ha]
    exact (canonical33243 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2420 + difference 5 3) (sourceB2420 + difference 3 5) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5069) := by
    have ha : (tripleCharges (sourceA2420 + difference 5 3) (sourceB2420 + difference 3 5) sourceC2420) = raw33244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33244; decide +kernel
    rw [ha]
    exact (canonical33244 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2420 + difference 5 4) (sourceB2420 + difference 4 5) sourceC2420) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5069) := by
    have ha : (tripleCharges (sourceA2420 + difference 5 4) (sourceB2420 + difference 4 5) sourceC2420) = raw33245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2420 sourceB2420 sourceC2420 difference raw33245; decide +kernel
    rw [ha]
    exact (canonical33245 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2420 sourceB2420 sourceC2420
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2420, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2421 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2421 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC2421 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceForm2421 : Integer.Sparse Master := [(Sum.inr 4307, 1), (Sum.inr 4309, 1), (Sum.inr 4310, 1), (Sum.inr 4313, 1), (Sum.inr 4503, 1), (Sum.inr 4917, 1), (Sum.inr 4919, 1), (Sum.inr 4920, 1), (Sum.inr 4922, 1), (Sum.inr 5027, 1), (Sum.inr 5028, 1), (Sum.inr 5030, 1), (Sum.inr 5076, 1), (Sum.inr 5078, 1), (Sum.inr 5080, 1), (Sum.inr 5093, 1), (Sum.inr 5094, 1), (Sum.inr 5095, 1), (Sum.inr 5105, 2), (Sum.inr 5109, 1), (Sum.inr 5110, 1), (Sum.inr 5294, 1), (Sum.inr 5304, 1), (Sum.inr 5310, 1), (Sum.inr 5370, 1), (Sum.inr 5422, 1), (Sum.inr 5434, 1), (Sum.inr 5451, 1), (Sum.inr 5484, 1)]

theorem sourceEq2421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2421 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2421 + difference 0 1) (sourceB2421 + difference 1 0) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2421 + difference 0 1) (sourceB2421 + difference 1 0) sourceC2421) = raw19000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw19000; decide +kernel
    rw [ha]
    exact (canonical19000 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2421 + difference 0 2) (sourceB2421 + difference 2 0) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA2421 + difference 0 2) (sourceB2421 + difference 2 0) sourceC2421) = raw19001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw19001; decide +kernel
    rw [ha]
    exact (canonical19001 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2421 + difference 0 3) (sourceB2421 + difference 3 0) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2421 + difference 0 3) (sourceB2421 + difference 3 0) sourceC2421) = raw8002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw8002; decide +kernel
    rw [ha]
    exact (canonical8002 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2421 + difference 0 4) (sourceB2421 + difference 4 0) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2421 + difference 0 4) (sourceB2421 + difference 4 0) sourceC2421) = raw19002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw19002; decide +kernel
    rw [ha]
    exact (canonical19002 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2421 + difference 0 5) (sourceB2421 + difference 5 0) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA2421 + difference 0 5) (sourceB2421 + difference 5 0) sourceC2421) = raw13969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw13969; decide +kernel
    rw [ha]
    exact (canonical13969 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2421 + difference 1 0) (sourceB2421 + difference 0 1) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA2421 + difference 1 0) (sourceB2421 + difference 0 1) sourceC2421) = raw8017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw8017; decide +kernel
    rw [ha]
    exact (canonical8017 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2421 + difference 1 2) (sourceB2421 + difference 2 1) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2421 + difference 1 2) (sourceB2421 + difference 2 1) sourceC2421) = raw8019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw8019; decide +kernel
    rw [ha]
    exact (canonical8019 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2421 + difference 1 3) (sourceB2421 + difference 3 1) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2421 + difference 1 3) (sourceB2421 + difference 3 1) sourceC2421) = raw13990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw13990; decide +kernel
    rw [ha]
    exact (canonical13990 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2421 + difference 1 4) (sourceB2421 + difference 4 1) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA2421 + difference 1 4) (sourceB2421 + difference 4 1) sourceC2421) = raw8020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw8020; decide +kernel
    rw [ha]
    exact (canonical8020 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2421 + difference 1 5) (sourceB2421 + difference 5 1) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA2421 + difference 1 5) (sourceB2421 + difference 5 1) sourceC2421) = raw8021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw8021; decide +kernel
    rw [ha]
    exact (canonical8021 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2421 + difference 2 0) (sourceB2421 + difference 0 2) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4307) := by
    have ha : (tripleCharges (sourceA2421 + difference 2 0) (sourceB2421 + difference 0 2) sourceC2421) = raw25667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw25667; decide +kernel
    rw [ha]
    exact (canonical25667 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2421 + difference 2 1) (sourceB2421 + difference 1 2) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4917) := by
    have ha : (tripleCharges (sourceA2421 + difference 2 1) (sourceB2421 + difference 1 2) sourceC2421) = raw33246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw33246; decide +kernel
    rw [ha]
    exact (canonical33246 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2421 + difference 2 3) (sourceB2421 + difference 3 2) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2421 + difference 2 3) (sourceB2421 + difference 3 2) sourceC2421) = raw8013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw8013; decide +kernel
    rw [ha]
    exact (canonical8013 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2421 + difference 2 4) (sourceB2421 + difference 4 2) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2421 + difference 2 4) (sourceB2421 + difference 4 2) sourceC2421) = raw33247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw33247; decide +kernel
    rw [ha]
    exact (canonical33247 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2421 + difference 2 5) (sourceB2421 + difference 5 2) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5093) := by
    have ha : (tripleCharges (sourceA2421 + difference 2 5) (sourceB2421 + difference 5 2) sourceC2421) = raw13978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw13978; decide +kernel
    rw [ha]
    exact (canonical13978 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2421 + difference 3 0) (sourceB2421 + difference 0 3) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA2421 + difference 3 0) (sourceB2421 + difference 0 3) sourceC2421) = raw25670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw25670; decide +kernel
    rw [ha]
    exact (canonical25670 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2421 + difference 3 1) (sourceB2421 + difference 1 3) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4920) := by
    have ha : (tripleCharges (sourceA2421 + difference 3 1) (sourceB2421 + difference 1 3) sourceC2421) = raw33248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw33248; decide +kernel
    rw [ha]
    exact (canonical33248 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2421 + difference 3 2) (sourceB2421 + difference 2 3) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5028) := by
    have ha : (tripleCharges (sourceA2421 + difference 3 2) (sourceB2421 + difference 2 3) sourceC2421) = raw33249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw33249; decide +kernel
    rw [ha]
    exact (canonical33249 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2421 + difference 3 4) (sourceB2421 + difference 4 3) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2421 + difference 3 4) (sourceB2421 + difference 4 3) sourceC2421) = raw33250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw33250; decide +kernel
    rw [ha]
    exact (canonical33250 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2421 + difference 3 5) (sourceB2421 + difference 5 3) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA2421 + difference 3 5) (sourceB2421 + difference 5 3) sourceC2421) = raw13982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw13982; decide +kernel
    rw [ha]
    exact (canonical13982 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2421 + difference 4 0) (sourceB2421 + difference 0 4) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4313) := by
    have ha : (tripleCharges (sourceA2421 + difference 4 0) (sourceB2421 + difference 0 4) sourceC2421) = raw25674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw25674; decide +kernel
    rw [ha]
    exact (canonical25674 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2421 + difference 4 1) (sourceB2421 + difference 1 4) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4922) := by
    have ha : (tripleCharges (sourceA2421 + difference 4 1) (sourceB2421 + difference 1 4) sourceC2421) = raw33251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw33251; decide +kernel
    rw [ha]
    exact (canonical33251 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2421 + difference 4 2) (sourceB2421 + difference 2 4) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5030) := by
    have ha : (tripleCharges (sourceA2421 + difference 4 2) (sourceB2421 + difference 2 4) sourceC2421) = raw33252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw33252; decide +kernel
    rw [ha]
    exact (canonical33252 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2421 + difference 4 3) (sourceB2421 + difference 3 4) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2421 + difference 4 3) (sourceB2421 + difference 3 4) sourceC2421) = raw8023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw8023; decide +kernel
    rw [ha]
    exact (canonical8023 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2421 + difference 4 5) (sourceB2421 + difference 5 4) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2421 + difference 4 5) (sourceB2421 + difference 5 4) sourceC2421) = raw13987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw13987; decide +kernel
    rw [ha]
    exact (canonical13987 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2421 + difference 5 0) (sourceB2421 + difference 0 5) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA2421 + difference 5 0) (sourceB2421 + difference 0 5) sourceC2421) = raw25677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw25677; decide +kernel
    rw [ha]
    exact (canonical25677 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2421 + difference 5 1) (sourceB2421 + difference 1 5) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4919) := by
    have ha : (tripleCharges (sourceA2421 + difference 5 1) (sourceB2421 + difference 1 5) sourceC2421) = raw33253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw33253; decide +kernel
    rw [ha]
    exact (canonical33253 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2421 + difference 5 2) (sourceB2421 + difference 2 5) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5027) := by
    have ha : (tripleCharges (sourceA2421 + difference 5 2) (sourceB2421 + difference 2 5) sourceC2421) = raw33254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw33254; decide +kernel
    rw [ha]
    exact (canonical33254 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2421 + difference 5 3) (sourceB2421 + difference 3 5) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2421 + difference 5 3) (sourceB2421 + difference 3 5) sourceC2421) = raw8028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw8028; decide +kernel
    rw [ha]
    exact (canonical8028 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2421 + difference 5 4) (sourceB2421 + difference 4 5) sourceC2421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2421 + difference 5 4) (sourceB2421 + difference 4 5) sourceC2421) = raw33255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2421 sourceB2421 sourceC2421 difference raw33255; decide +kernel
    rw [ha]
    exact (canonical33255 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2421 sourceB2421 sourceC2421
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2421, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2422 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2422 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC2422 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceForm2422 : Integer.Sparse Master := [(Sum.inr 885, 1), (Sum.inr 887, 1), (Sum.inr 888, 1), (Sum.inr 891, 1), (Sum.inr 1087, 1), (Sum.inr 2308, 1), (Sum.inr 2310, 1), (Sum.inr 2311, 1), (Sum.inr 2313, 1), (Sum.inr 2416, 1), (Sum.inr 2417, 1), (Sum.inr 2419, 1), (Sum.inr 2483, 1), (Sum.inr 2485, 1), (Sum.inr 2488, 1), (Sum.inr 2503, 1), (Sum.inr 2504, 1), (Sum.inr 2505, 1), (Sum.inr 2515, 2), (Sum.inr 2519, 1), (Sum.inr 2522, 1), (Sum.inr 2768, 1), (Sum.inr 2782, 1), (Sum.inr 2788, 1), (Sum.inr 3706, 1), (Sum.inr 3964, 1), (Sum.inr 3982, 1), (Sum.inr 3983, 1), (Sum.inr 3987, 1)]

theorem sourceEq2422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2422 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2422 + difference 0 1) (sourceB2422 + difference 1 0) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2422 + difference 0 1) (sourceB2422 + difference 1 0) sourceC2422) = raw33256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33256; decide +kernel
    rw [ha]
    exact (canonical33256 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2422 + difference 0 2) (sourceB2422 + difference 2 0) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA2422 + difference 0 2) (sourceB2422 + difference 2 0) sourceC2422) = raw33257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33257; decide +kernel
    rw [ha]
    exact (canonical33257 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2422 + difference 0 3) (sourceB2422 + difference 3 0) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA2422 + difference 0 3) (sourceB2422 + difference 3 0) sourceC2422) = raw8032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw8032; decide +kernel
    rw [ha]
    exact (canonical8032 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2422 + difference 0 4) (sourceB2422 + difference 4 0) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA2422 + difference 0 4) (sourceB2422 + difference 4 0) sourceC2422) = raw33258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33258; decide +kernel
    rw [ha]
    exact (canonical33258 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2422 + difference 0 5) (sourceB2422 + difference 5 0) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA2422 + difference 0 5) (sourceB2422 + difference 5 0) sourceC2422) = raw13991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw13991; decide +kernel
    rw [ha]
    exact (canonical13991 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2422 + difference 1 0) (sourceB2422 + difference 0 1) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA2422 + difference 1 0) (sourceB2422 + difference 0 1) sourceC2422) = raw8047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw8047; decide +kernel
    rw [ha]
    exact (canonical8047 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2422 + difference 1 2) (sourceB2422 + difference 2 1) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2422 + difference 1 2) (sourceB2422 + difference 2 1) sourceC2422) = raw8049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw8049; decide +kernel
    rw [ha]
    exact (canonical8049 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2422 + difference 1 3) (sourceB2422 + difference 3 1) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA2422 + difference 1 3) (sourceB2422 + difference 3 1) sourceC2422) = raw14012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw14012; decide +kernel
    rw [ha]
    exact (canonical14012 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2422 + difference 1 4) (sourceB2422 + difference 4 1) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA2422 + difference 1 4) (sourceB2422 + difference 4 1) sourceC2422) = raw8050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw8050; decide +kernel
    rw [ha]
    exact (canonical8050 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2422 + difference 1 5) (sourceB2422 + difference 5 1) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA2422 + difference 1 5) (sourceB2422 + difference 5 1) sourceC2422) = raw8051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw8051; decide +kernel
    rw [ha]
    exact (canonical8051 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2422 + difference 2 0) (sourceB2422 + difference 0 2) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 885) := by
    have ha : (tripleCharges (sourceA2422 + difference 2 0) (sourceB2422 + difference 0 2) sourceC2422) = raw25684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw25684; decide +kernel
    rw [ha]
    exact (canonical25684 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2422 + difference 2 1) (sourceB2422 + difference 1 2) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2308) := by
    have ha : (tripleCharges (sourceA2422 + difference 2 1) (sourceB2422 + difference 1 2) sourceC2422) = raw33259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33259; decide +kernel
    rw [ha]
    exact (canonical33259 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2422 + difference 2 3) (sourceB2422 + difference 3 2) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA2422 + difference 2 3) (sourceB2422 + difference 3 2) sourceC2422) = raw8043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw8043; decide +kernel
    rw [ha]
    exact (canonical8043 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2422 + difference 2 4) (sourceB2422 + difference 4 2) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2422 + difference 2 4) (sourceB2422 + difference 4 2) sourceC2422) = raw33260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33260; decide +kernel
    rw [ha]
    exact (canonical33260 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2422 + difference 2 5) (sourceB2422 + difference 5 2) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2503) := by
    have ha : (tripleCharges (sourceA2422 + difference 2 5) (sourceB2422 + difference 5 2) sourceC2422) = raw14000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw14000; decide +kernel
    rw [ha]
    exact (canonical14000 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2422 + difference 3 0) (sourceB2422 + difference 0 3) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA2422 + difference 3 0) (sourceB2422 + difference 0 3) sourceC2422) = raw25687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw25687; decide +kernel
    rw [ha]
    exact (canonical25687 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2422 + difference 3 1) (sourceB2422 + difference 1 3) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2311) := by
    have ha : (tripleCharges (sourceA2422 + difference 3 1) (sourceB2422 + difference 1 3) sourceC2422) = raw33261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33261; decide +kernel
    rw [ha]
    exact (canonical33261 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2422 + difference 3 2) (sourceB2422 + difference 2 3) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2417) := by
    have ha : (tripleCharges (sourceA2422 + difference 3 2) (sourceB2422 + difference 2 3) sourceC2422) = raw33262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33262; decide +kernel
    rw [ha]
    exact (canonical33262 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2422 + difference 3 4) (sourceB2422 + difference 4 3) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA2422 + difference 3 4) (sourceB2422 + difference 4 3) sourceC2422) = raw33263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33263; decide +kernel
    rw [ha]
    exact (canonical33263 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2422 + difference 3 5) (sourceB2422 + difference 5 3) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2504) := by
    have ha : (tripleCharges (sourceA2422 + difference 3 5) (sourceB2422 + difference 5 3) sourceC2422) = raw14004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw14004; decide +kernel
    rw [ha]
    exact (canonical14004 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2422 + difference 4 0) (sourceB2422 + difference 0 4) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 891) := by
    have ha : (tripleCharges (sourceA2422 + difference 4 0) (sourceB2422 + difference 0 4) sourceC2422) = raw25691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw25691; decide +kernel
    rw [ha]
    exact (canonical25691 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2422 + difference 4 1) (sourceB2422 + difference 1 4) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2313) := by
    have ha : (tripleCharges (sourceA2422 + difference 4 1) (sourceB2422 + difference 1 4) sourceC2422) = raw33264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33264; decide +kernel
    rw [ha]
    exact (canonical33264 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2422 + difference 4 2) (sourceB2422 + difference 2 4) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2419) := by
    have ha : (tripleCharges (sourceA2422 + difference 4 2) (sourceB2422 + difference 2 4) sourceC2422) = raw33265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33265; decide +kernel
    rw [ha]
    exact (canonical33265 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2422 + difference 4 3) (sourceB2422 + difference 3 4) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2422 + difference 4 3) (sourceB2422 + difference 3 4) sourceC2422) = raw8053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw8053; decide +kernel
    rw [ha]
    exact (canonical8053 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2422 + difference 4 5) (sourceB2422 + difference 5 4) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA2422 + difference 4 5) (sourceB2422 + difference 5 4) sourceC2422) = raw14009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw14009; decide +kernel
    rw [ha]
    exact (canonical14009 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2422 + difference 5 0) (sourceB2422 + difference 0 5) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA2422 + difference 5 0) (sourceB2422 + difference 0 5) sourceC2422) = raw25694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw25694; decide +kernel
    rw [ha]
    exact (canonical25694 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2422 + difference 5 1) (sourceB2422 + difference 1 5) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2310) := by
    have ha : (tripleCharges (sourceA2422 + difference 5 1) (sourceB2422 + difference 1 5) sourceC2422) = raw33266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33266; decide +kernel
    rw [ha]
    exact (canonical33266 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2422 + difference 5 2) (sourceB2422 + difference 2 5) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2416) := by
    have ha : (tripleCharges (sourceA2422 + difference 5 2) (sourceB2422 + difference 2 5) sourceC2422) = raw33267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33267; decide +kernel
    rw [ha]
    exact (canonical33267 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2422 + difference 5 3) (sourceB2422 + difference 3 5) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA2422 + difference 5 3) (sourceB2422 + difference 3 5) sourceC2422) = raw8058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw8058; decide +kernel
    rw [ha]
    exact (canonical8058 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2422 + difference 5 4) (sourceB2422 + difference 4 5) sourceC2422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA2422 + difference 5 4) (sourceB2422 + difference 4 5) sourceC2422) = raw33268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2422 sourceB2422 sourceC2422 difference raw33268; decide +kernel
    rw [ha]
    exact (canonical33268 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2422 sourceB2422 sourceC2422
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2422, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2423 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2423 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2423 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceForm2423 : Integer.Sparse Master := [(Sum.inr 4301, 1), (Sum.inr 4303, 1), (Sum.inr 4304, 1), (Sum.inr 4314, 1), (Sum.inr 4499, 1), (Sum.inr 4912, 1), (Sum.inr 4913, 1), (Sum.inr 4914, 1), (Sum.inr 4923, 1), (Sum.inr 4986, 1), (Sum.inr 4989, 1), (Sum.inr 5000, 1), (Sum.inr 5014, 1), (Sum.inr 5031, 1), (Sum.inr 5059, 1), (Sum.inr 5073, 1), (Sum.inr 5075, 1), (Sum.inr 5081, 1), (Sum.inr 5098, 1), (Sum.inr 5099, 1), (Sum.inr 5102, 2), (Sum.inr 5275, 1), (Sum.inr 5293, 1), (Sum.inr 5306, 1), (Sum.inr 5368, 1), (Sum.inr 5469, 1), (Sum.inr 5473, 1), (Sum.inr 5483, 1), (Sum.inr 5485, 1)]

theorem sourceEq2423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2423 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2423 + difference 0 1) (sourceB2423 + difference 1 0) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2423 + difference 0 1) (sourceB2423 + difference 1 0) sourceC2423) = raw33269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33269; decide +kernel
    rw [ha]
    exact (canonical33269 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2423 + difference 0 2) (sourceB2423 + difference 2 0) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA2423 + difference 0 2) (sourceB2423 + difference 2 0) sourceC2423) = raw33270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33270; decide +kernel
    rw [ha]
    exact (canonical33270 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2423 + difference 0 3) (sourceB2423 + difference 3 0) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2423 + difference 0 3) (sourceB2423 + difference 3 0) sourceC2423) = raw3257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw3257; decide +kernel
    rw [ha]
    exact (canonical3257 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2423 + difference 0 4) (sourceB2423 + difference 4 0) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2423 + difference 0 4) (sourceB2423 + difference 4 0) sourceC2423) = raw33271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33271; decide +kernel
    rw [ha]
    exact (canonical33271 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2423 + difference 0 5) (sourceB2423 + difference 5 0) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2423 + difference 0 5) (sourceB2423 + difference 5 0) sourceC2423) = raw3247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw3247; decide +kernel
    rw [ha]
    exact (canonical3247 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2423 + difference 1 0) (sourceB2423 + difference 0 1) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA2423 + difference 1 0) (sourceB2423 + difference 0 1) sourceC2423) = raw7875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw7875; decide +kernel
    rw [ha]
    exact (canonical7875 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2423 + difference 1 2) (sourceB2423 + difference 2 1) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2423 + difference 1 2) (sourceB2423 + difference 2 1) sourceC2423) = raw7877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw7877; decide +kernel
    rw [ha]
    exact (canonical7877 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2423 + difference 1 3) (sourceB2423 + difference 3 1) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2423 + difference 1 3) (sourceB2423 + difference 3 1) sourceC2423) = raw3256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw3256; decide +kernel
    rw [ha]
    exact (canonical3256 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2423 + difference 1 4) (sourceB2423 + difference 4 1) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2423 + difference 1 4) (sourceB2423 + difference 4 1) sourceC2423) = raw7878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw7878; decide +kernel
    rw [ha]
    exact (canonical7878 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2423 + difference 1 5) (sourceB2423 + difference 5 1) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA2423 + difference 1 5) (sourceB2423 + difference 5 1) sourceC2423) = raw3246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw3246; decide +kernel
    rw [ha]
    exact (canonical3246 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2423 + difference 2 0) (sourceB2423 + difference 0 2) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA2423 + difference 2 0) (sourceB2423 + difference 0 2) sourceC2423) = raw25798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw25798; decide +kernel
    rw [ha]
    exact (canonical25798 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2423 + difference 2 1) (sourceB2423 + difference 1 2) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2423 + difference 2 1) (sourceB2423 + difference 1 2) sourceC2423) = raw33272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33272; decide +kernel
    rw [ha]
    exact (canonical33272 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2423 + difference 2 3) (sourceB2423 + difference 3 2) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2423 + difference 2 3) (sourceB2423 + difference 3 2) sourceC2423) = raw7872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw7872; decide +kernel
    rw [ha]
    exact (canonical7872 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2423 + difference 2 4) (sourceB2423 + difference 4 2) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA2423 + difference 2 4) (sourceB2423 + difference 4 2) sourceC2423) = raw33273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33273; decide +kernel
    rw [ha]
    exact (canonical33273 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2423 + difference 2 5) (sourceB2423 + difference 5 2) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA2423 + difference 2 5) (sourceB2423 + difference 5 2) sourceC2423) = raw33274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33274; decide +kernel
    rw [ha]
    exact (canonical33274 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2423 + difference 3 0) (sourceB2423 + difference 0 3) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA2423 + difference 3 0) (sourceB2423 + difference 0 3) sourceC2423) = raw25802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw25802; decide +kernel
    rw [ha]
    exact (canonical25802 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2423 + difference 3 1) (sourceB2423 + difference 1 3) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2423 + difference 3 1) (sourceB2423 + difference 1 3) sourceC2423) = raw33275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33275; decide +kernel
    rw [ha]
    exact (canonical33275 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2423 + difference 3 2) (sourceB2423 + difference 2 3) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4989) := by
    have ha : (tripleCharges (sourceA2423 + difference 3 2) (sourceB2423 + difference 2 3) sourceC2423) = raw33276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33276; decide +kernel
    rw [ha]
    exact (canonical33276 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2423 + difference 3 4) (sourceB2423 + difference 4 3) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2423 + difference 3 4) (sourceB2423 + difference 4 3) sourceC2423) = raw33277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33277; decide +kernel
    rw [ha]
    exact (canonical33277 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2423 + difference 3 5) (sourceB2423 + difference 5 3) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2423 + difference 3 5) (sourceB2423 + difference 5 3) sourceC2423) = raw33278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33278; decide +kernel
    rw [ha]
    exact (canonical33278 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2423 + difference 4 0) (sourceB2423 + difference 0 4) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4314) := by
    have ha : (tripleCharges (sourceA2423 + difference 4 0) (sourceB2423 + difference 0 4) sourceC2423) = raw25807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw25807; decide +kernel
    rw [ha]
    exact (canonical25807 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2423 + difference 4 1) (sourceB2423 + difference 1 4) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4923) := by
    have ha : (tripleCharges (sourceA2423 + difference 4 1) (sourceB2423 + difference 1 4) sourceC2423) = raw33279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33279; decide +kernel
    rw [ha]
    exact (canonical33279 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2423 + difference 4 2) (sourceB2423 + difference 2 4) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5031) := by
    have ha : (tripleCharges (sourceA2423 + difference 4 2) (sourceB2423 + difference 2 4) sourceC2423) = raw33280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33280; decide +kernel
    rw [ha]
    exact (canonical33280 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2423 + difference 4 3) (sourceB2423 + difference 3 4) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2423 + difference 4 3) (sourceB2423 + difference 3 4) sourceC2423) = raw7880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw7880; decide +kernel
    rw [ha]
    exact (canonical7880 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2423 + difference 4 5) (sourceB2423 + difference 5 4) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2423 + difference 4 5) (sourceB2423 + difference 5 4) sourceC2423) = raw33281 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33281; decide +kernel
    rw [ha]
    exact (canonical33281 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2423 + difference 5 0) (sourceB2423 + difference 0 5) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4303) := by
    have ha : (tripleCharges (sourceA2423 + difference 5 0) (sourceB2423 + difference 0 5) sourceC2423) = raw25811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw25811; decide +kernel
    rw [ha]
    exact (canonical25811 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2423 + difference 5 1) (sourceB2423 + difference 1 5) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2423 + difference 5 1) (sourceB2423 + difference 1 5) sourceC2423) = raw33282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33282; decide +kernel
    rw [ha]
    exact (canonical33282 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2423 + difference 5 2) (sourceB2423 + difference 2 5) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4986) := by
    have ha : (tripleCharges (sourceA2423 + difference 5 2) (sourceB2423 + difference 2 5) sourceC2423) = raw33283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33283; decide +kernel
    rw [ha]
    exact (canonical33283 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2423 + difference 5 3) (sourceB2423 + difference 3 5) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2423 + difference 5 3) (sourceB2423 + difference 3 5) sourceC2423) = raw7884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw7884; decide +kernel
    rw [ha]
    exact (canonical7884 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2423 + difference 5 4) (sourceB2423 + difference 4 5) sourceC2423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2423 + difference 5 4) (sourceB2423 + difference 4 5) sourceC2423) = raw33284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2423 sourceB2423 sourceC2423 difference raw33284; decide +kernel
    rw [ha]
    exact (canonical33284 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2423 sourceB2423 sourceC2423
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2423, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2424 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2424 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2424 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceForm2424 : Integer.Sparse Master := [(Sum.inr 879, 1), (Sum.inr 881, 1), (Sum.inr 882, 1), (Sum.inr 892, 1), (Sum.inr 1083, 1), (Sum.inr 2305, 1), (Sum.inr 2306, 1), (Sum.inr 2307, 1), (Sum.inr 2314, 1), (Sum.inr 2371, 1), (Sum.inr 2385, 1), (Sum.inr 2413, 1), (Sum.inr 2420, 1), (Sum.inr 2462, 1), (Sum.inr 2467, 1), (Sum.inr 2480, 1), (Sum.inr 2482, 1), (Sum.inr 2489, 1), (Sum.inr 2508, 1), (Sum.inr 2509, 1), (Sum.inr 2512, 2), (Sum.inr 2743, 1), (Sum.inr 2767, 1), (Sum.inr 2784, 1), (Sum.inr 3705, 1), (Sum.inr 3945, 1), (Sum.inr 3958, 1), (Sum.inr 3981, 1), (Sum.inr 3984, 1)]

theorem sourceEq2424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2424 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2424 + difference 0 1) (sourceB2424 + difference 1 0) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA2424 + difference 0 1) (sourceB2424 + difference 1 0) sourceC2424) = raw33285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33285; decide +kernel
    rw [ha]
    exact (canonical33285 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2424 + difference 0 2) (sourceB2424 + difference 2 0) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3945) := by
    have ha : (tripleCharges (sourceA2424 + difference 0 2) (sourceB2424 + difference 2 0) sourceC2424) = raw33286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33286; decide +kernel
    rw [ha]
    exact (canonical33286 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2424 + difference 0 3) (sourceB2424 + difference 3 0) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2424 + difference 0 3) (sourceB2424 + difference 3 0) sourceC2424) = raw7888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw7888; decide +kernel
    rw [ha]
    exact (canonical7888 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2424 + difference 0 4) (sourceB2424 + difference 4 0) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA2424 + difference 0 4) (sourceB2424 + difference 4 0) sourceC2424) = raw33287 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33287; decide +kernel
    rw [ha]
    exact (canonical33287 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2424 + difference 0 5) (sourceB2424 + difference 5 0) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA2424 + difference 0 5) (sourceB2424 + difference 5 0) sourceC2424) = raw33288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33288; decide +kernel
    rw [ha]
    exact (canonical33288 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2424 + difference 1 0) (sourceB2424 + difference 0 1) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA2424 + difference 1 0) (sourceB2424 + difference 0 1) sourceC2424) = raw7903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw7903; decide +kernel
    rw [ha]
    exact (canonical7903 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2424 + difference 1 2) (sourceB2424 + difference 2 1) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2424 + difference 1 2) (sourceB2424 + difference 2 1) sourceC2424) = raw7905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw7905; decide +kernel
    rw [ha]
    exact (canonical7905 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2424 + difference 1 3) (sourceB2424 + difference 3 1) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA2424 + difference 1 3) (sourceB2424 + difference 3 1) sourceC2424) = raw25814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw25814; decide +kernel
    rw [ha]
    exact (canonical25814 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2424 + difference 1 4) (sourceB2424 + difference 4 1) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2424 + difference 1 4) (sourceB2424 + difference 4 1) sourceC2424) = raw7906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw7906; decide +kernel
    rw [ha]
    exact (canonical7906 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2424 + difference 1 5) (sourceB2424 + difference 5 1) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA2424 + difference 1 5) (sourceB2424 + difference 5 1) sourceC2424) = raw7907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw7907; decide +kernel
    rw [ha]
    exact (canonical7907 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2424 + difference 2 0) (sourceB2424 + difference 0 2) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 879) := by
    have ha : (tripleCharges (sourceA2424 + difference 2 0) (sourceB2424 + difference 0 2) sourceC2424) = raw25820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw25820; decide +kernel
    rw [ha]
    exact (canonical25820 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2424 + difference 2 1) (sourceB2424 + difference 1 2) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2305) := by
    have ha : (tripleCharges (sourceA2424 + difference 2 1) (sourceB2424 + difference 1 2) sourceC2424) = raw33289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33289; decide +kernel
    rw [ha]
    exact (canonical33289 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2424 + difference 2 3) (sourceB2424 + difference 3 2) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA2424 + difference 2 3) (sourceB2424 + difference 3 2) sourceC2424) = raw7899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw7899; decide +kernel
    rw [ha]
    exact (canonical7899 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2424 + difference 2 4) (sourceB2424 + difference 4 2) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA2424 + difference 2 4) (sourceB2424 + difference 4 2) sourceC2424) = raw33290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33290; decide +kernel
    rw [ha]
    exact (canonical33290 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2424 + difference 2 5) (sourceB2424 + difference 5 2) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA2424 + difference 2 5) (sourceB2424 + difference 5 2) sourceC2424) = raw33291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33291; decide +kernel
    rw [ha]
    exact (canonical33291 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2424 + difference 3 0) (sourceB2424 + difference 0 3) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA2424 + difference 3 0) (sourceB2424 + difference 0 3) sourceC2424) = raw25824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw25824; decide +kernel
    rw [ha]
    exact (canonical25824 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2424 + difference 3 1) (sourceB2424 + difference 1 3) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2307) := by
    have ha : (tripleCharges (sourceA2424 + difference 3 1) (sourceB2424 + difference 1 3) sourceC2424) = raw33292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33292; decide +kernel
    rw [ha]
    exact (canonical33292 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2424 + difference 3 2) (sourceB2424 + difference 2 3) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2413) := by
    have ha : (tripleCharges (sourceA2424 + difference 3 2) (sourceB2424 + difference 2 3) sourceC2424) = raw33293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33293; decide +kernel
    rw [ha]
    exact (canonical33293 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2424 + difference 3 4) (sourceB2424 + difference 4 3) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA2424 + difference 3 4) (sourceB2424 + difference 4 3) sourceC2424) = raw33294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33294; decide +kernel
    rw [ha]
    exact (canonical33294 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2424 + difference 3 5) (sourceB2424 + difference 5 3) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA2424 + difference 3 5) (sourceB2424 + difference 5 3) sourceC2424) = raw33295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33295; decide +kernel
    rw [ha]
    exact (canonical33295 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2424 + difference 4 0) (sourceB2424 + difference 0 4) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 892) := by
    have ha : (tripleCharges (sourceA2424 + difference 4 0) (sourceB2424 + difference 0 4) sourceC2424) = raw25829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw25829; decide +kernel
    rw [ha]
    exact (canonical25829 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2424 + difference 4 1) (sourceB2424 + difference 1 4) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2314) := by
    have ha : (tripleCharges (sourceA2424 + difference 4 1) (sourceB2424 + difference 1 4) sourceC2424) = raw33296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33296; decide +kernel
    rw [ha]
    exact (canonical33296 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2424 + difference 4 2) (sourceB2424 + difference 2 4) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2420) := by
    have ha : (tripleCharges (sourceA2424 + difference 4 2) (sourceB2424 + difference 2 4) sourceC2424) = raw33297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33297; decide +kernel
    rw [ha]
    exact (canonical33297 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2424 + difference 4 3) (sourceB2424 + difference 3 4) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2424 + difference 4 3) (sourceB2424 + difference 3 4) sourceC2424) = raw7909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw7909; decide +kernel
    rw [ha]
    exact (canonical7909 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2424 + difference 4 5) (sourceB2424 + difference 5 4) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2424 + difference 4 5) (sourceB2424 + difference 5 4) sourceC2424) = raw33298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33298; decide +kernel
    rw [ha]
    exact (canonical33298 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2424 + difference 5 0) (sourceB2424 + difference 0 5) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 881) := by
    have ha : (tripleCharges (sourceA2424 + difference 5 0) (sourceB2424 + difference 0 5) sourceC2424) = raw25833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw25833; decide +kernel
    rw [ha]
    exact (canonical25833 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2424 + difference 5 1) (sourceB2424 + difference 1 5) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2306) := by
    have ha : (tripleCharges (sourceA2424 + difference 5 1) (sourceB2424 + difference 1 5) sourceC2424) = raw33299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33299; decide +kernel
    rw [ha]
    exact (canonical33299 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2424 + difference 5 2) (sourceB2424 + difference 2 5) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2371) := by
    have ha : (tripleCharges (sourceA2424 + difference 5 2) (sourceB2424 + difference 2 5) sourceC2424) = raw33300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33300; decide +kernel
    rw [ha]
    exact (canonical33300 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2424 + difference 5 3) (sourceB2424 + difference 3 5) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2424 + difference 5 3) (sourceB2424 + difference 3 5) sourceC2424) = raw7914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw7914; decide +kernel
    rw [ha]
    exact (canonical7914 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2424 + difference 5 4) (sourceB2424 + difference 4 5) sourceC2424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA2424 + difference 5 4) (sourceB2424 + difference 4 5) sourceC2424) = raw33301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2424 sourceB2424 sourceC2424 difference raw33301; decide +kernel
    rw [ha]
    exact (canonical33301 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2424 sourceB2424 sourceC2424
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2424, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2425 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2425 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2425 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceForm2425 : Integer.Sparse Master := [(Sum.inr 4540, 1), (Sum.inr 4543, 1), (Sum.inr 4548, 2), (Sum.inr 4600, 1), (Sum.inr 4760, 1), (Sum.inr 4769, 1), (Sum.inr 4841, 2), (Sum.inr 4938, 1), (Sum.inr 4945, 2), (Sum.inr 5035, 2), (Sum.inr 5097, 1), (Sum.inr 5099, 2), (Sum.inr 5103, 2), (Sum.inr 5110, 2), (Sum.inr 5133, 1), (Sum.inr 5241, 1), (Sum.inr 5248, 1), (Sum.inr 5270, 1), (Sum.inr 5272, 2), (Sum.inr 5274, 2), (Sum.inr 5284, 1)]

theorem sourceEq2425 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2425 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2425 + difference 0 1) (sourceB2425 + difference 1 0) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2425 + difference 0 1) (sourceB2425 + difference 1 0) sourceC2425) = raw33302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33302; decide +kernel
    rw [ha]
    exact (canonical33302 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2425 + difference 0 2) (sourceB2425 + difference 2 0) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2425 + difference 0 2) (sourceB2425 + difference 2 0) sourceC2425) = raw33303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33303; decide +kernel
    rw [ha]
    exact (canonical33303 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2425 + difference 0 3) (sourceB2425 + difference 3 0) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2425 + difference 0 3) (sourceB2425 + difference 3 0) sourceC2425) = raw29067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw29067; decide +kernel
    rw [ha]
    exact (canonical29067 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2425 + difference 0 4) (sourceB2425 + difference 4 0) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2425 + difference 0 4) (sourceB2425 + difference 4 0) sourceC2425) = raw33304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33304; decide +kernel
    rw [ha]
    exact (canonical33304 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2425 + difference 0 5) (sourceB2425 + difference 5 0) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA2425 + difference 0 5) (sourceB2425 + difference 5 0) sourceC2425) = raw33305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33305; decide +kernel
    rw [ha]
    exact (canonical33305 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2425 + difference 1 0) (sourceB2425 + difference 0 1) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA2425 + difference 1 0) (sourceB2425 + difference 0 1) sourceC2425) = raw33306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33306; decide +kernel
    rw [ha]
    exact (canonical33306 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2425 + difference 1 2) (sourceB2425 + difference 2 1) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5133) := by
    have ha : (tripleCharges (sourceA2425 + difference 1 2) (sourceB2425 + difference 2 1) sourceC2425) = raw33307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33307; decide +kernel
    rw [ha]
    exact (canonical33307 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2425 + difference 1 3) (sourceB2425 + difference 3 1) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA2425 + difference 1 3) (sourceB2425 + difference 3 1) sourceC2425) = raw29072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw29072; decide +kernel
    rw [ha]
    exact (canonical29072 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2425 + difference 1 4) (sourceB2425 + difference 4 1) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA2425 + difference 1 4) (sourceB2425 + difference 4 1) sourceC2425) = raw33308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33308; decide +kernel
    rw [ha]
    exact (canonical33308 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2425 + difference 1 5) (sourceB2425 + difference 5 1) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA2425 + difference 1 5) (sourceB2425 + difference 5 1) sourceC2425) = raw33309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33309; decide +kernel
    rw [ha]
    exact (canonical33309 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2425 + difference 2 0) (sourceB2425 + difference 0 2) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4540) := by
    have ha : (tripleCharges (sourceA2425 + difference 2 0) (sourceB2425 + difference 0 2) sourceC2425) = raw33310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33310; decide +kernel
    rw [ha]
    exact (canonical33310 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2425 + difference 2 1) (sourceB2425 + difference 1 2) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4938) := by
    have ha : (tripleCharges (sourceA2425 + difference 2 1) (sourceB2425 + difference 1 2) sourceC2425) = raw33311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33311; decide +kernel
    rw [ha]
    exact (canonical33311 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2425 + difference 2 3) (sourceB2425 + difference 3 2) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2425 + difference 2 3) (sourceB2425 + difference 3 2) sourceC2425) = raw29077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw29077; decide +kernel
    rw [ha]
    exact (canonical29077 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2425 + difference 2 4) (sourceB2425 + difference 4 2) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2425 + difference 2 4) (sourceB2425 + difference 4 2) sourceC2425) = raw33312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33312; decide +kernel
    rw [ha]
    exact (canonical33312 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2425 + difference 2 5) (sourceB2425 + difference 5 2) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5097) := by
    have ha : (tripleCharges (sourceA2425 + difference 2 5) (sourceB2425 + difference 5 2) sourceC2425) = raw33313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33313; decide +kernel
    rw [ha]
    exact (canonical33313 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2425 + difference 3 0) (sourceB2425 + difference 0 3) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4548) := by
    have ha : (tripleCharges (sourceA2425 + difference 3 0) (sourceB2425 + difference 0 3) sourceC2425) = raw33314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33314; decide +kernel
    rw [ha]
    exact (canonical33314 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2425 + difference 3 1) (sourceB2425 + difference 1 3) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2425 + difference 3 1) (sourceB2425 + difference 1 3) sourceC2425) = raw33315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33315; decide +kernel
    rw [ha]
    exact (canonical33315 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2425 + difference 3 2) (sourceB2425 + difference 2 3) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5035) := by
    have ha : (tripleCharges (sourceA2425 + difference 3 2) (sourceB2425 + difference 2 3) sourceC2425) = raw33316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33316; decide +kernel
    rw [ha]
    exact (canonical33316 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2425 + difference 3 4) (sourceB2425 + difference 4 3) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2425 + difference 3 4) (sourceB2425 + difference 4 3) sourceC2425) = raw33317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33317; decide +kernel
    rw [ha]
    exact (canonical33317 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2425 + difference 3 5) (sourceB2425 + difference 5 3) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA2425 + difference 3 5) (sourceB2425 + difference 5 3) sourceC2425) = raw33318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33318; decide +kernel
    rw [ha]
    exact (canonical33318 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2425 + difference 4 0) (sourceB2425 + difference 0 4) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4548) := by
    have ha : (tripleCharges (sourceA2425 + difference 4 0) (sourceB2425 + difference 0 4) sourceC2425) = raw33319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33319; decide +kernel
    rw [ha]
    exact (canonical33319 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2425 + difference 4 1) (sourceB2425 + difference 1 4) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2425 + difference 4 1) (sourceB2425 + difference 1 4) sourceC2425) = raw33320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33320; decide +kernel
    rw [ha]
    exact (canonical33320 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2425 + difference 4 2) (sourceB2425 + difference 2 4) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5035) := by
    have ha : (tripleCharges (sourceA2425 + difference 4 2) (sourceB2425 + difference 2 4) sourceC2425) = raw33321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33321; decide +kernel
    rw [ha]
    exact (canonical33321 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2425 + difference 4 3) (sourceB2425 + difference 3 4) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2425 + difference 4 3) (sourceB2425 + difference 3 4) sourceC2425) = raw29087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw29087; decide +kernel
    rw [ha]
    exact (canonical29087 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2425 + difference 4 5) (sourceB2425 + difference 5 4) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA2425 + difference 4 5) (sourceB2425 + difference 5 4) sourceC2425) = raw33322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33322; decide +kernel
    rw [ha]
    exact (canonical33322 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2425 + difference 5 0) (sourceB2425 + difference 0 5) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA2425 + difference 5 0) (sourceB2425 + difference 0 5) sourceC2425) = raw29078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw29078; decide +kernel
    rw [ha]
    exact (canonical29078 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2425 + difference 5 1) (sourceB2425 + difference 1 5) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2425 + difference 5 1) (sourceB2425 + difference 1 5) sourceC2425) = raw29079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw29079; decide +kernel
    rw [ha]
    exact (canonical29079 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2425 + difference 5 2) (sourceB2425 + difference 2 5) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2425 + difference 5 2) (sourceB2425 + difference 2 5) sourceC2425) = raw29080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw29080; decide +kernel
    rw [ha]
    exact (canonical29080 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2425 + difference 5 3) (sourceB2425 + difference 3 5) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2425 + difference 5 3) (sourceB2425 + difference 3 5) sourceC2425) = raw33323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw33323; decide +kernel
    rw [ha]
    exact (canonical33323 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2425 + difference 5 4) (sourceB2425 + difference 4 5) sourceC2425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2425 + difference 5 4) (sourceB2425 + difference 4 5) sourceC2425) = raw29081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2425 sourceB2425 sourceC2425 difference raw29081; decide +kernel
    rw [ha]
    exact (canonical29081 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2425 sourceB2425 sourceC2425
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2425, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2426 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2426 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2426 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceForm2426 : Integer.Sparse Master := [(Sum.inr 2173, 1), (Sum.inr 2184, 1), (Sum.inr 2185, 1), (Sum.inr 2228, 2), (Sum.inr 2652, 2), (Sum.inr 2657, 2), (Sum.inr 2658, 2), (Sum.inr 2685, 2), (Sum.inr 2688, 1), (Sum.inr 2689, 1), (Sum.inr 2693, 1), (Sum.inr 2694, 1), (Sum.inr 2702, 1), (Sum.inr 2704, 2), (Sum.inr 2705, 1), (Sum.inr 2740, 2), (Sum.inr 2742, 2), (Sum.inr 3024, 2), (Sum.inr 3058, 1), (Sum.inr 3075, 1), (Sum.inr 3077, 1)]

theorem sourceEq2426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2426 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2426 + difference 0 1) (sourceB2426 + difference 1 0) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2426 + difference 0 1) (sourceB2426 + difference 1 0) sourceC2426) = raw33324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33324; decide +kernel
    rw [ha]
    exact (canonical33324 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2426 + difference 0 2) (sourceB2426 + difference 2 0) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA2426 + difference 0 2) (sourceB2426 + difference 2 0) sourceC2426) = raw33325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33325; decide +kernel
    rw [ha]
    exact (canonical33325 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2426 + difference 0 3) (sourceB2426 + difference 3 0) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2426 + difference 0 3) (sourceB2426 + difference 3 0) sourceC2426) = raw29097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29097; decide +kernel
    rw [ha]
    exact (canonical29097 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2426 + difference 0 4) (sourceB2426 + difference 4 0) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2426 + difference 0 4) (sourceB2426 + difference 4 0) sourceC2426) = raw33326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33326; decide +kernel
    rw [ha]
    exact (canonical33326 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2426 + difference 0 5) (sourceB2426 + difference 5 0) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA2426 + difference 0 5) (sourceB2426 + difference 5 0) sourceC2426) = raw33327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33327; decide +kernel
    rw [ha]
    exact (canonical33327 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2426 + difference 1 0) (sourceB2426 + difference 0 1) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA2426 + difference 1 0) (sourceB2426 + difference 0 1) sourceC2426) = raw33328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33328; decide +kernel
    rw [ha]
    exact (canonical33328 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2426 + difference 1 2) (sourceB2426 + difference 2 1) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA2426 + difference 1 2) (sourceB2426 + difference 2 1) sourceC2426) = raw33329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33329; decide +kernel
    rw [ha]
    exact (canonical33329 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2426 + difference 1 3) (sourceB2426 + difference 3 1) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2426 + difference 1 3) (sourceB2426 + difference 3 1) sourceC2426) = raw29102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29102; decide +kernel
    rw [ha]
    exact (canonical29102 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2426 + difference 1 4) (sourceB2426 + difference 4 1) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2426 + difference 1 4) (sourceB2426 + difference 4 1) sourceC2426) = raw33330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33330; decide +kernel
    rw [ha]
    exact (canonical33330 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2426 + difference 1 5) (sourceB2426 + difference 5 1) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA2426 + difference 1 5) (sourceB2426 + difference 5 1) sourceC2426) = raw33331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33331; decide +kernel
    rw [ha]
    exact (canonical33331 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2426 + difference 2 0) (sourceB2426 + difference 0 2) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2688) := by
    have ha : (tripleCharges (sourceA2426 + difference 2 0) (sourceB2426 + difference 0 2) sourceC2426) = raw33332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33332; decide +kernel
    rw [ha]
    exact (canonical33332 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2426 + difference 2 1) (sourceB2426 + difference 1 2) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2689) := by
    have ha : (tripleCharges (sourceA2426 + difference 2 1) (sourceB2426 + difference 1 2) sourceC2426) = raw33333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33333; decide +kernel
    rw [ha]
    exact (canonical33333 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2426 + difference 2 3) (sourceB2426 + difference 3 2) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2426 + difference 2 3) (sourceB2426 + difference 3 2) sourceC2426) = raw29107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29107; decide +kernel
    rw [ha]
    exact (canonical29107 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2426 + difference 2 4) (sourceB2426 + difference 4 2) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2426 + difference 2 4) (sourceB2426 + difference 4 2) sourceC2426) = raw33334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33334; decide +kernel
    rw [ha]
    exact (canonical33334 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2426 + difference 2 5) (sourceB2426 + difference 5 2) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA2426 + difference 2 5) (sourceB2426 + difference 5 2) sourceC2426) = raw33335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33335; decide +kernel
    rw [ha]
    exact (canonical33335 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2426 + difference 3 0) (sourceB2426 + difference 0 3) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2426 + difference 3 0) (sourceB2426 + difference 0 3) sourceC2426) = raw33336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33336; decide +kernel
    rw [ha]
    exact (canonical33336 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2426 + difference 3 1) (sourceB2426 + difference 1 3) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2426 + difference 3 1) (sourceB2426 + difference 1 3) sourceC2426) = raw33337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33337; decide +kernel
    rw [ha]
    exact (canonical33337 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2426 + difference 3 2) (sourceB2426 + difference 2 3) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2426 + difference 3 2) (sourceB2426 + difference 2 3) sourceC2426) = raw33338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33338; decide +kernel
    rw [ha]
    exact (canonical33338 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2426 + difference 3 4) (sourceB2426 + difference 4 3) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2426 + difference 3 4) (sourceB2426 + difference 4 3) sourceC2426) = raw33339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33339; decide +kernel
    rw [ha]
    exact (canonical33339 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2426 + difference 3 5) (sourceB2426 + difference 5 3) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA2426 + difference 3 5) (sourceB2426 + difference 5 3) sourceC2426) = raw33340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33340; decide +kernel
    rw [ha]
    exact (canonical33340 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2426 + difference 4 0) (sourceB2426 + difference 0 4) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2426 + difference 4 0) (sourceB2426 + difference 0 4) sourceC2426) = raw33341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33341; decide +kernel
    rw [ha]
    exact (canonical33341 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2426 + difference 4 1) (sourceB2426 + difference 1 4) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2426 + difference 4 1) (sourceB2426 + difference 1 4) sourceC2426) = raw33342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33342; decide +kernel
    rw [ha]
    exact (canonical33342 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2426 + difference 4 2) (sourceB2426 + difference 2 4) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2426 + difference 4 2) (sourceB2426 + difference 2 4) sourceC2426) = raw33343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33343; decide +kernel
    rw [ha]
    exact (canonical33343 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2426 + difference 4 3) (sourceB2426 + difference 3 4) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2426 + difference 4 3) (sourceB2426 + difference 3 4) sourceC2426) = raw29117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29117; decide +kernel
    rw [ha]
    exact (canonical29117 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2426 + difference 4 5) (sourceB2426 + difference 5 4) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA2426 + difference 4 5) (sourceB2426 + difference 5 4) sourceC2426) = raw33344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33344; decide +kernel
    rw [ha]
    exact (canonical33344 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2426 + difference 5 0) (sourceB2426 + difference 0 5) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA2426 + difference 5 0) (sourceB2426 + difference 0 5) sourceC2426) = raw29108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29108; decide +kernel
    rw [ha]
    exact (canonical29108 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2426 + difference 5 1) (sourceB2426 + difference 1 5) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2426 + difference 5 1) (sourceB2426 + difference 1 5) sourceC2426) = raw29109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29109; decide +kernel
    rw [ha]
    exact (canonical29109 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2426 + difference 5 2) (sourceB2426 + difference 2 5) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2173) := by
    have ha : (tripleCharges (sourceA2426 + difference 5 2) (sourceB2426 + difference 2 5) sourceC2426) = raw29110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29110; decide +kernel
    rw [ha]
    exact (canonical29110 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2426 + difference 5 3) (sourceB2426 + difference 3 5) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2426 + difference 5 3) (sourceB2426 + difference 3 5) sourceC2426) = raw33345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33345; decide +kernel
    rw [ha]
    exact (canonical33345 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2426 + difference 5 4) (sourceB2426 + difference 4 5) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2426 + difference 5 4) (sourceB2426 + difference 4 5) sourceC2426) = raw29111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29111; decide +kernel
    rw [ha]
    exact (canonical29111 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2426 sourceB2426 sourceC2426
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2426, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2427 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2427 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2427 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceForm2427 : Integer.Sparse Master := [(Sum.inr 4297, 1), (Sum.inr 4299, 1), (Sum.inr 4304, 2), (Sum.inr 4386, 1), (Sum.inr 4389, 1), (Sum.inr 4418, 2), (Sum.inr 4496, 1), (Sum.inr 4909, 1), (Sum.inr 4914, 2), (Sum.inr 4989, 2), (Sum.inr 5014, 2), (Sum.inr 5055, 2), (Sum.inr 5098, 1), (Sum.inr 5099, 1), (Sum.inr 5102, 2), (Sum.inr 5247, 1), (Sum.inr 5248, 1), (Sum.inr 5271, 2), (Sum.inr 5272, 2), (Sum.inr 5306, 1), (Sum.inr 5485, 1)]

theorem sourceEq2427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2427 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2427 + difference 0 1) (sourceB2427 + difference 1 0) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2427 + difference 0 1) (sourceB2427 + difference 1 0) sourceC2427) = raw18681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw18681; decide +kernel
    rw [ha]
    exact (canonical18681 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2427 + difference 0 2) (sourceB2427 + difference 2 0) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA2427 + difference 0 2) (sourceB2427 + difference 2 0) sourceC2427) = raw18682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw18682; decide +kernel
    rw [ha]
    exact (canonical18682 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2427 + difference 0 3) (sourceB2427 + difference 3 0) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2427 + difference 0 3) (sourceB2427 + difference 3 0) sourceC2427) = raw10672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw10672; decide +kernel
    rw [ha]
    exact (canonical10672 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2427 + difference 0 4) (sourceB2427 + difference 4 0) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2427 + difference 0 4) (sourceB2427 + difference 4 0) sourceC2427) = raw18683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw18683; decide +kernel
    rw [ha]
    exact (canonical18683 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2427 + difference 0 5) (sourceB2427 + difference 5 0) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2427 + difference 0 5) (sourceB2427 + difference 5 0) sourceC2427) = raw12131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw12131; decide +kernel
    rw [ha]
    exact (canonical12131 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2427 + difference 1 0) (sourceB2427 + difference 0 1) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA2427 + difference 1 0) (sourceB2427 + difference 0 1) sourceC2427) = raw10687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw10687; decide +kernel
    rw [ha]
    exact (canonical10687 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2427 + difference 1 2) (sourceB2427 + difference 2 1) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2427 + difference 1 2) (sourceB2427 + difference 2 1) sourceC2427) = raw10689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw10689; decide +kernel
    rw [ha]
    exact (canonical10689 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2427 + difference 1 3) (sourceB2427 + difference 3 1) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA2427 + difference 1 3) (sourceB2427 + difference 3 1) sourceC2427) = raw12152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw12152; decide +kernel
    rw [ha]
    exact (canonical12152 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2427 + difference 1 4) (sourceB2427 + difference 4 1) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA2427 + difference 1 4) (sourceB2427 + difference 4 1) sourceC2427) = raw10690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw10690; decide +kernel
    rw [ha]
    exact (canonical10690 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2427 + difference 1 5) (sourceB2427 + difference 5 1) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA2427 + difference 1 5) (sourceB2427 + difference 5 1) sourceC2427) = raw10691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw10691; decide +kernel
    rw [ha]
    exact (canonical10691 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2427 + difference 2 0) (sourceB2427 + difference 0 2) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4297) := by
    have ha : (tripleCharges (sourceA2427 + difference 2 0) (sourceB2427 + difference 0 2) sourceC2427) = raw26006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw26006; decide +kernel
    rw [ha]
    exact (canonical26006 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2427 + difference 2 1) (sourceB2427 + difference 1 2) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4909) := by
    have ha : (tripleCharges (sourceA2427 + difference 2 1) (sourceB2427 + difference 1 2) sourceC2427) = raw33346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw33346; decide +kernel
    rw [ha]
    exact (canonical33346 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2427 + difference 2 3) (sourceB2427 + difference 3 2) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA2427 + difference 2 3) (sourceB2427 + difference 3 2) sourceC2427) = raw10683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw10683; decide +kernel
    rw [ha]
    exact (canonical10683 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2427 + difference 2 4) (sourceB2427 + difference 4 2) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA2427 + difference 2 4) (sourceB2427 + difference 4 2) sourceC2427) = raw33347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw33347; decide +kernel
    rw [ha]
    exact (canonical33347 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2427 + difference 2 5) (sourceB2427 + difference 5 2) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA2427 + difference 2 5) (sourceB2427 + difference 5 2) sourceC2427) = raw12140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw12140; decide +kernel
    rw [ha]
    exact (canonical12140 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2427 + difference 3 0) (sourceB2427 + difference 0 3) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA2427 + difference 3 0) (sourceB2427 + difference 0 3) sourceC2427) = raw26009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw26009; decide +kernel
    rw [ha]
    exact (canonical26009 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2427 + difference 3 1) (sourceB2427 + difference 1 3) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2427 + difference 3 1) (sourceB2427 + difference 1 3) sourceC2427) = raw33348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw33348; decide +kernel
    rw [ha]
    exact (canonical33348 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2427 + difference 3 2) (sourceB2427 + difference 2 3) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4989) := by
    have ha : (tripleCharges (sourceA2427 + difference 3 2) (sourceB2427 + difference 2 3) sourceC2427) = raw33349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw33349; decide +kernel
    rw [ha]
    exact (canonical33349 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2427 + difference 3 4) (sourceB2427 + difference 4 3) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2427 + difference 3 4) (sourceB2427 + difference 4 3) sourceC2427) = raw33350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw33350; decide +kernel
    rw [ha]
    exact (canonical33350 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2427 + difference 3 5) (sourceB2427 + difference 5 3) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2427 + difference 3 5) (sourceB2427 + difference 5 3) sourceC2427) = raw12144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw12144; decide +kernel
    rw [ha]
    exact (canonical12144 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2427 + difference 4 0) (sourceB2427 + difference 0 4) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA2427 + difference 4 0) (sourceB2427 + difference 0 4) sourceC2427) = raw26013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw26013; decide +kernel
    rw [ha]
    exact (canonical26013 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2427 + difference 4 1) (sourceB2427 + difference 1 4) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2427 + difference 4 1) (sourceB2427 + difference 1 4) sourceC2427) = raw33351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw33351; decide +kernel
    rw [ha]
    exact (canonical33351 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2427 + difference 4 2) (sourceB2427 + difference 2 4) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4989) := by
    have ha : (tripleCharges (sourceA2427 + difference 4 2) (sourceB2427 + difference 2 4) sourceC2427) = raw33352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw33352; decide +kernel
    rw [ha]
    exact (canonical33352 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2427 + difference 4 3) (sourceB2427 + difference 3 4) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2427 + difference 4 3) (sourceB2427 + difference 3 4) sourceC2427) = raw10693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw10693; decide +kernel
    rw [ha]
    exact (canonical10693 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2427 + difference 4 5) (sourceB2427 + difference 5 4) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2427 + difference 4 5) (sourceB2427 + difference 5 4) sourceC2427) = raw12149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw12149; decide +kernel
    rw [ha]
    exact (canonical12149 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2427 + difference 5 0) (sourceB2427 + difference 0 5) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4299) := by
    have ha : (tripleCharges (sourceA2427 + difference 5 0) (sourceB2427 + difference 0 5) sourceC2427) = raw26016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw26016; decide +kernel
    rw [ha]
    exact (canonical26016 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2427 + difference 5 1) (sourceB2427 + difference 1 5) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4389) := by
    have ha : (tripleCharges (sourceA2427 + difference 5 1) (sourceB2427 + difference 1 5) sourceC2427) = raw33353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw33353; decide +kernel
    rw [ha]
    exact (canonical33353 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2427 + difference 5 2) (sourceB2427 + difference 2 5) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4386) := by
    have ha : (tripleCharges (sourceA2427 + difference 5 2) (sourceB2427 + difference 2 5) sourceC2427) = raw33354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw33354; decide +kernel
    rw [ha]
    exact (canonical33354 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2427 + difference 5 3) (sourceB2427 + difference 3 5) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA2427 + difference 5 3) (sourceB2427 + difference 3 5) sourceC2427) = raw10698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw10698; decide +kernel
    rw [ha]
    exact (canonical10698 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2427 + difference 5 4) (sourceB2427 + difference 4 5) sourceC2427) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA2427 + difference 5 4) (sourceB2427 + difference 4 5) sourceC2427) = raw33355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2427 sourceB2427 sourceC2427 difference raw33355; decide +kernel
    rw [ha]
    exact (canonical33355 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2427 sourceB2427 sourceC2427
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2427, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2428 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2428 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2428 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceForm2428 : Integer.Sparse Master := [(Sum.inr 875, 1), (Sum.inr 877, 1), (Sum.inr 882, 2), (Sum.inr 1080, 1), (Sum.inr 1582, 1), (Sum.inr 1585, 1), (Sum.inr 1602, 2), (Sum.inr 2302, 1), (Sum.inr 2307, 2), (Sum.inr 2413, 2), (Sum.inr 2458, 2), (Sum.inr 2467, 2), (Sum.inr 2508, 1), (Sum.inr 2509, 1), (Sum.inr 2512, 2), (Sum.inr 2740, 2), (Sum.inr 2784, 1), (Sum.inr 3496, 1), (Sum.inr 3498, 1), (Sum.inr 3534, 2), (Sum.inr 3984, 1)]

theorem sourceEq2428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2428 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2428 + difference 0 1) (sourceB2428 + difference 1 0) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3498) := by
    have ha : (tripleCharges (sourceA2428 + difference 0 1) (sourceB2428 + difference 1 0) sourceC2428) = raw33356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33356; decide +kernel
    rw [ha]
    exact (canonical33356 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2428 + difference 0 2) (sourceB2428 + difference 2 0) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3496) := by
    have ha : (tripleCharges (sourceA2428 + difference 0 2) (sourceB2428 + difference 2 0) sourceC2428) = raw33357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33357; decide +kernel
    rw [ha]
    exact (canonical33357 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2428 + difference 0 3) (sourceB2428 + difference 3 0) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA2428 + difference 0 3) (sourceB2428 + difference 3 0) sourceC2428) = raw33358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33358; decide +kernel
    rw [ha]
    exact (canonical33358 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2428 + difference 0 4) (sourceB2428 + difference 4 0) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA2428 + difference 0 4) (sourceB2428 + difference 4 0) sourceC2428) = raw33359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33359; decide +kernel
    rw [ha]
    exact (canonical33359 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2428 + difference 0 5) (sourceB2428 + difference 5 0) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA2428 + difference 0 5) (sourceB2428 + difference 5 0) sourceC2428) = raw12153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw12153; decide +kernel
    rw [ha]
    exact (canonical12153 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2428 + difference 1 0) (sourceB2428 + difference 0 1) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA2428 + difference 1 0) (sourceB2428 + difference 0 1) sourceC2428) = raw12178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw12178; decide +kernel
    rw [ha]
    exact (canonical12178 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2428 + difference 1 2) (sourceB2428 + difference 2 1) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA2428 + difference 1 2) (sourceB2428 + difference 2 1) sourceC2428) = raw12180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw12180; decide +kernel
    rw [ha]
    exact (canonical12180 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2428 + difference 1 3) (sourceB2428 + difference 3 1) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2428 + difference 1 3) (sourceB2428 + difference 3 1) sourceC2428) = raw12181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw12181; decide +kernel
    rw [ha]
    exact (canonical12181 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2428 + difference 1 4) (sourceB2428 + difference 4 1) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2428 + difference 1 4) (sourceB2428 + difference 4 1) sourceC2428) = raw12182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw12182; decide +kernel
    rw [ha]
    exact (canonical12182 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2428 + difference 1 5) (sourceB2428 + difference 5 1) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA2428 + difference 1 5) (sourceB2428 + difference 5 1) sourceC2428) = raw26019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw26019; decide +kernel
    rw [ha]
    exact (canonical26019 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2428 + difference 2 0) (sourceB2428 + difference 0 2) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 875) := by
    have ha : (tripleCharges (sourceA2428 + difference 2 0) (sourceB2428 + difference 0 2) sourceC2428) = raw26025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw26025; decide +kernel
    rw [ha]
    exact (canonical26025 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2428 + difference 2 1) (sourceB2428 + difference 1 2) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2302) := by
    have ha : (tripleCharges (sourceA2428 + difference 2 1) (sourceB2428 + difference 1 2) sourceC2428) = raw33360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33360; decide +kernel
    rw [ha]
    exact (canonical33360 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2428 + difference 2 3) (sourceB2428 + difference 3 2) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2458) := by
    have ha : (tripleCharges (sourceA2428 + difference 2 3) (sourceB2428 + difference 3 2) sourceC2428) = raw33361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33361; decide +kernel
    rw [ha]
    exact (canonical33361 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2428 + difference 2 4) (sourceB2428 + difference 4 2) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2458) := by
    have ha : (tripleCharges (sourceA2428 + difference 2 4) (sourceB2428 + difference 4 2) sourceC2428) = raw33362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33362; decide +kernel
    rw [ha]
    exact (canonical33362 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2428 + difference 2 5) (sourceB2428 + difference 5 2) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA2428 + difference 2 5) (sourceB2428 + difference 5 2) sourceC2428) = raw12164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw12164; decide +kernel
    rw [ha]
    exact (canonical12164 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2428 + difference 3 0) (sourceB2428 + difference 0 3) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA2428 + difference 3 0) (sourceB2428 + difference 0 3) sourceC2428) = raw26029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw26029; decide +kernel
    rw [ha]
    exact (canonical26029 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2428 + difference 3 1) (sourceB2428 + difference 1 3) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2307) := by
    have ha : (tripleCharges (sourceA2428 + difference 3 1) (sourceB2428 + difference 1 3) sourceC2428) = raw33363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33363; decide +kernel
    rw [ha]
    exact (canonical33363 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2428 + difference 3 2) (sourceB2428 + difference 2 3) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2413) := by
    have ha : (tripleCharges (sourceA2428 + difference 3 2) (sourceB2428 + difference 2 3) sourceC2428) = raw33364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33364; decide +kernel
    rw [ha]
    exact (canonical33364 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2428 + difference 3 4) (sourceB2428 + difference 4 3) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA2428 + difference 3 4) (sourceB2428 + difference 4 3) sourceC2428) = raw33365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33365; decide +kernel
    rw [ha]
    exact (canonical33365 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2428 + difference 3 5) (sourceB2428 + difference 5 3) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2428 + difference 3 5) (sourceB2428 + difference 5 3) sourceC2428) = raw12169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw12169; decide +kernel
    rw [ha]
    exact (canonical12169 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2428 + difference 4 0) (sourceB2428 + difference 0 4) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA2428 + difference 4 0) (sourceB2428 + difference 0 4) sourceC2428) = raw26033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw26033; decide +kernel
    rw [ha]
    exact (canonical26033 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2428 + difference 4 1) (sourceB2428 + difference 1 4) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2307) := by
    have ha : (tripleCharges (sourceA2428 + difference 4 1) (sourceB2428 + difference 1 4) sourceC2428) = raw33366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33366; decide +kernel
    rw [ha]
    exact (canonical33366 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2428 + difference 4 2) (sourceB2428 + difference 2 4) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2413) := by
    have ha : (tripleCharges (sourceA2428 + difference 4 2) (sourceB2428 + difference 2 4) sourceC2428) = raw33367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33367; decide +kernel
    rw [ha]
    exact (canonical33367 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2428 + difference 4 3) (sourceB2428 + difference 3 4) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA2428 + difference 4 3) (sourceB2428 + difference 3 4) sourceC2428) = raw33368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33368; decide +kernel
    rw [ha]
    exact (canonical33368 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2428 + difference 4 5) (sourceB2428 + difference 5 4) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2428 + difference 4 5) (sourceB2428 + difference 5 4) sourceC2428) = raw12174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw12174; decide +kernel
    rw [ha]
    exact (canonical12174 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2428 + difference 5 0) (sourceB2428 + difference 0 5) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 877) := by
    have ha : (tripleCharges (sourceA2428 + difference 5 0) (sourceB2428 + difference 0 5) sourceC2428) = raw26037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw26037; decide +kernel
    rw [ha]
    exact (canonical26037 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2428 + difference 5 1) (sourceB2428 + difference 1 5) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1585) := by
    have ha : (tripleCharges (sourceA2428 + difference 5 1) (sourceB2428 + difference 1 5) sourceC2428) = raw33369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33369; decide +kernel
    rw [ha]
    exact (canonical33369 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2428 + difference 5 2) (sourceB2428 + difference 2 5) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1582) := by
    have ha : (tripleCharges (sourceA2428 + difference 5 2) (sourceB2428 + difference 2 5) sourceC2428) = raw33370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33370; decide +kernel
    rw [ha]
    exact (canonical33370 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2428 + difference 5 3) (sourceB2428 + difference 3 5) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA2428 + difference 5 3) (sourceB2428 + difference 3 5) sourceC2428) = raw33371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33371; decide +kernel
    rw [ha]
    exact (canonical33371 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2428 + difference 5 4) (sourceB2428 + difference 4 5) sourceC2428) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA2428 + difference 5 4) (sourceB2428 + difference 4 5) sourceC2428) = raw33372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2428 sourceB2428 sourceC2428 difference raw33372; decide +kernel
    rw [ha]
    exact (canonical33372 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2428 sourceB2428 sourceC2428
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2428, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2429 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2429 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC2429 : Charge := ![2, 1, 1, -2, -1, -1]
def sourceForm2429 : Integer.Sparse Master := [(Sum.inr 2416, 1), (Sum.inr 2418, 1), (Sum.inr 2420, 1), (Sum.inr 2462, 2), (Sum.inr 3777, 1), (Sum.inr 4090, -1)]

theorem sourceEq2429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2429 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2429 + difference 0 2) (sourceB2429 + difference 2 0) sourceC2429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3777) := by
    have ha : (tripleCharges (sourceA2429 + difference 0 2) (sourceB2429 + difference 2 0) sourceC2429) = raw33373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2429 sourceB2429 sourceC2429 difference raw33373; decide +kernel
    rw [ha]
    exact (canonical33373 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2429 + difference 1 2) (sourceB2429 + difference 2 1) sourceC2429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA2429 + difference 1 2) (sourceB2429 + difference 2 1) sourceC2429) = raw24877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2429 sourceB2429 sourceC2429 difference raw24877; decide +kernel
    rw [ha]
    exact (canonical24877 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2429 + difference 2 2) (sourceB2429 + difference 2 2) sourceC2429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA2429 + difference 2 2) (sourceB2429 + difference 2 2) sourceC2429) = raw24876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2429 sourceB2429 sourceC2429 difference raw24876; decide +kernel
    rw [ha]
    exact (canonical24876 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2429 + difference 3 2) (sourceB2429 + difference 2 3) sourceC2429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2418) := by
    have ha : (tripleCharges (sourceA2429 + difference 3 2) (sourceB2429 + difference 2 3) sourceC2429) = raw33374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2429 sourceB2429 sourceC2429 difference raw33374; decide +kernel
    rw [ha]
    exact (canonical33374 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2429 + difference 4 2) (sourceB2429 + difference 2 4) sourceC2429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2420) := by
    have ha : (tripleCharges (sourceA2429 + difference 4 2) (sourceB2429 + difference 2 4) sourceC2429) = raw33375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2429 sourceB2429 sourceC2429 difference raw33375; decide +kernel
    rw [ha]
    exact (canonical33375 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2429 + difference 5 2) (sourceB2429 + difference 2 5) sourceC2429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2416) := by
    have ha : (tripleCharges (sourceA2429 + difference 5 2) (sourceB2429 + difference 2 5) sourceC2429) = raw33376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2429 sourceB2429 sourceC2429 difference raw33376; decide +kernel
    rw [ha]
    exact (canonical33376 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2429 + sourceB2429) sourceC2429) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2429 + sourceB2429) sourceC2429) = raw24881 := by
      apply Matrix.ext; unfold doubleCharges sourceA2429 sourceB2429 sourceC2429 raw24881; decide +kernel
    rw [ha]
    exact (canonical24881 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2429 sourceB2429 sourceC2429
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2429, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2430 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceB2430 : Charge := ![2, 1, 1, -2, -1, -1]
def sourceC2430 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2430 : Integer.Sparse Master := [(Sum.inr 1867, 1), (Sum.inr 1869, 1), (Sum.inr 1871, 1), (Sum.inr 1947, 1), (Sum.inr 2000, 1), (Sum.inr 3436, 1), (Sum.inr 4080, -1)]

theorem sourceEq2430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2430 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2430 + difference 0 0) (sourceB2430 + difference 0 0) sourceC2430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3436) := by
    have ha : (tripleCharges (sourceA2430 + difference 0 0) (sourceB2430 + difference 0 0) sourceC2430) = raw33377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2430 sourceB2430 sourceC2430 difference raw33377; decide +kernel
    rw [ha]
    exact (canonical33377 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2430 + difference 1 0) (sourceB2430 + difference 0 1) sourceC2430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2000) := by
    have ha : (tripleCharges (sourceA2430 + difference 1 0) (sourceB2430 + difference 0 1) sourceC2430) = raw33378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2430 sourceB2430 sourceC2430 difference raw33378; decide +kernel
    rw [ha]
    exact (canonical33378 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2430 + difference 2 0) (sourceB2430 + difference 0 2) sourceC2430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1947) := by
    have ha : (tripleCharges (sourceA2430 + difference 2 0) (sourceB2430 + difference 0 2) sourceC2430) = raw33379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2430 sourceB2430 sourceC2430 difference raw33379; decide +kernel
    rw [ha]
    exact (canonical33379 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2430 + difference 3 0) (sourceB2430 + difference 0 3) sourceC2430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1867) := by
    have ha : (tripleCharges (sourceA2430 + difference 3 0) (sourceB2430 + difference 0 3) sourceC2430) = raw33380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2430 sourceB2430 sourceC2430 difference raw33380; decide +kernel
    rw [ha]
    exact (canonical33380 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2430 + difference 4 0) (sourceB2430 + difference 0 4) sourceC2430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1871) := by
    have ha : (tripleCharges (sourceA2430 + difference 4 0) (sourceB2430 + difference 0 4) sourceC2430) = raw33381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2430 sourceB2430 sourceC2430 difference raw33381; decide +kernel
    rw [ha]
    exact (canonical33381 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2430 + difference 5 0) (sourceB2430 + difference 0 5) sourceC2430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1869) := by
    have ha : (tripleCharges (sourceA2430 + difference 5 0) (sourceB2430 + difference 0 5) sourceC2430) = raw33382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2430 sourceB2430 sourceC2430 difference raw33382; decide +kernel
    rw [ha]
    exact (canonical33382 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2430 + sourceB2430) sourceC2430) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2430 + sourceB2430) sourceC2430) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2430 sourceB2430 sourceC2430 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2430 sourceB2430 sourceC2430
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2430, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2431 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2431 : Charge := ![1, 0, -1, 1, -1, 0]
def sourceC2431 : Charge := ![2, 1, 1, -2, 0, -2]
def sourceForm2431 : Integer.Sparse Master := [(Sum.inr 2371, 1), (Sum.inr 2414, 1), (Sum.inr 2419, 1), (Sum.inr 2459, 2), (Sum.inr 3745, 1), (Sum.inr 4088, -1)]

theorem sourceEq2431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2431 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2431 + difference 0 2) (sourceB2431 + difference 2 0) sourceC2431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3745) := by
    have ha : (tripleCharges (sourceA2431 + difference 0 2) (sourceB2431 + difference 2 0) sourceC2431) = raw33383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2431 sourceB2431 sourceC2431 difference raw33383; decide +kernel
    rw [ha]
    exact (canonical33383 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2431 + difference 1 2) (sourceB2431 + difference 2 1) sourceC2431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA2431 + difference 1 2) (sourceB2431 + difference 2 1) sourceC2431) = raw24888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2431 sourceB2431 sourceC2431 difference raw24888; decide +kernel
    rw [ha]
    exact (canonical24888 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2431 + difference 2 2) (sourceB2431 + difference 2 2) sourceC2431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA2431 + difference 2 2) (sourceB2431 + difference 2 2) sourceC2431) = raw24887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2431 sourceB2431 sourceC2431 difference raw24887; decide +kernel
    rw [ha]
    exact (canonical24887 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2431 + difference 3 2) (sourceB2431 + difference 2 3) sourceC2431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2414) := by
    have ha : (tripleCharges (sourceA2431 + difference 3 2) (sourceB2431 + difference 2 3) sourceC2431) = raw33384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2431 sourceB2431 sourceC2431 difference raw33384; decide +kernel
    rw [ha]
    exact (canonical33384 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2431 + difference 4 2) (sourceB2431 + difference 2 4) sourceC2431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2419) := by
    have ha : (tripleCharges (sourceA2431 + difference 4 2) (sourceB2431 + difference 2 4) sourceC2431) = raw33385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2431 sourceB2431 sourceC2431 difference raw33385; decide +kernel
    rw [ha]
    exact (canonical33385 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2431 + difference 5 2) (sourceB2431 + difference 2 5) sourceC2431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2371) := by
    have ha : (tripleCharges (sourceA2431 + difference 5 2) (sourceB2431 + difference 2 5) sourceC2431) = raw33386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2431 sourceB2431 sourceC2431 difference raw33386; decide +kernel
    rw [ha]
    exact (canonical33386 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2431 + sourceB2431) sourceC2431) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2431 + sourceB2431) sourceC2431) = raw24892 := by
      apply Matrix.ext; unfold doubleCharges sourceA2431 sourceB2431 sourceC2431 raw24892; decide +kernel
    rw [ha]
    exact (canonical24892 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2431 sourceB2431 sourceC2431
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2431, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
