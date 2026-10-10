import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical57

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA352 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB352 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC352 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm352 : Integer.Sparse Master := [(Sum.inr 2120, 1), (Sum.inr 2121, 1), (Sum.inr 2122, 1), (Sum.inr 2133, 1), (Sum.inr 2196, 1), (Sum.inr 2216, 1), (Sum.inr 2217, 1), (Sum.inr 2221, 1), (Sum.inr 2279, 1), (Sum.inr 2666, 1), (Sum.inr 2678, 1), (Sum.inr 2679, 1), (Sum.inr 2698, 1), (Sum.inr 2699, 1), (Sum.inr 2710, 1), (Sum.inr 2714, 1), (Sum.inr 2715, 1), (Sum.inr 2723, 1), (Sum.inr 2724, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1), (Sum.inr 2733, 1), (Sum.inr 2768, 1), (Sum.inr 2776, 1), (Sum.inr 2777, 1), (Sum.inr 2942, 1), (Sum.inr 3045, 1), (Sum.inr 3069, 1), (Sum.inr 3089, 1), (Sum.inr 3094, 1)]

theorem sourceEq352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm352 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA352 + difference 0 1) (sourceB352 + difference 1 0) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3045) := by
    have ha : (tripleCharges (sourceA352 + difference 0 1) (sourceB352 + difference 1 0) sourceC352) = raw7064 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7064; decide +kernel
    rw [ha]
    exact (canonical7064 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA352 + difference 0 2) (sourceB352 + difference 2 0) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3069) := by
    have ha : (tripleCharges (sourceA352 + difference 0 2) (sourceB352 + difference 2 0) sourceC352) = raw7065 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7065; decide +kernel
    rw [ha]
    exact (canonical7065 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA352 + difference 0 3) (sourceB352 + difference 3 0) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA352 + difference 0 3) (sourceB352 + difference 3 0) sourceC352) = raw6393 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6393; decide +kernel
    rw [ha]
    exact (canonical6393 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA352 + difference 0 4) (sourceB352 + difference 4 0) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3094) := by
    have ha : (tripleCharges (sourceA352 + difference 0 4) (sourceB352 + difference 4 0) sourceC352) = raw6732 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6732; decide +kernel
    rw [ha]
    exact (canonical6732 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA352 + difference 0 5) (sourceB352 + difference 5 0) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA352 + difference 0 5) (sourceB352 + difference 5 0) sourceC352) = raw7066 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7066; decide +kernel
    rw [ha]
    exact (canonical7066 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA352 + difference 1 0) (sourceB352 + difference 0 1) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA352 + difference 1 0) (sourceB352 + difference 0 1) sourceC352) = raw7067 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7067; decide +kernel
    rw [ha]
    exact (canonical7067 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA352 + difference 1 2) (sourceB352 + difference 2 1) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA352 + difference 1 2) (sourceB352 + difference 2 1) sourceC352) = raw7068 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7068; decide +kernel
    rw [ha]
    exact (canonical7068 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA352 + difference 1 3) (sourceB352 + difference 3 1) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA352 + difference 1 3) (sourceB352 + difference 3 1) sourceC352) = raw6397 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6397; decide +kernel
    rw [ha]
    exact (canonical6397 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA352 + difference 1 4) (sourceB352 + difference 4 1) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA352 + difference 1 4) (sourceB352 + difference 4 1) sourceC352) = raw6737 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6737; decide +kernel
    rw [ha]
    exact (canonical6737 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA352 + difference 1 5) (sourceB352 + difference 5 1) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA352 + difference 1 5) (sourceB352 + difference 5 1) sourceC352) = raw7069 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7069; decide +kernel
    rw [ha]
    exact (canonical7069 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA352 + difference 2 0) (sourceB352 + difference 0 2) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA352 + difference 2 0) (sourceB352 + difference 0 2) sourceC352) = raw7070 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7070; decide +kernel
    rw [ha]
    exact (canonical7070 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA352 + difference 2 1) (sourceB352 + difference 1 2) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2666) := by
    have ha : (tripleCharges (sourceA352 + difference 2 1) (sourceB352 + difference 1 2) sourceC352) = raw7071 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7071; decide +kernel
    rw [ha]
    exact (canonical7071 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA352 + difference 2 3) (sourceB352 + difference 3 2) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA352 + difference 2 3) (sourceB352 + difference 3 2) sourceC352) = raw6401 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6401; decide +kernel
    rw [ha]
    exact (canonical6401 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA352 + difference 2 4) (sourceB352 + difference 4 2) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA352 + difference 2 4) (sourceB352 + difference 4 2) sourceC352) = raw6742 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6742; decide +kernel
    rw [ha]
    exact (canonical6742 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA352 + difference 2 5) (sourceB352 + difference 5 2) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2715) := by
    have ha : (tripleCharges (sourceA352 + difference 2 5) (sourceB352 + difference 5 2) sourceC352) = raw7072 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7072; decide +kernel
    rw [ha]
    exact (canonical7072 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA352 + difference 3 0) (sourceB352 + difference 0 3) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2221) := by
    have ha : (tripleCharges (sourceA352 + difference 3 0) (sourceB352 + difference 0 3) sourceC352) = raw7073 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7073; decide +kernel
    rw [ha]
    exact (canonical7073 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA352 + difference 3 1) (sourceB352 + difference 1 3) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2122) := by
    have ha : (tripleCharges (sourceA352 + difference 3 1) (sourceB352 + difference 1 3) sourceC352) = raw7074 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7074; decide +kernel
    rw [ha]
    exact (canonical7074 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA352 + difference 3 2) (sourceB352 + difference 2 3) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2120) := by
    have ha : (tripleCharges (sourceA352 + difference 3 2) (sourceB352 + difference 2 3) sourceC352) = raw7075 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7075; decide +kernel
    rw [ha]
    exact (canonical7075 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA352 + difference 3 4) (sourceB352 + difference 4 3) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA352 + difference 3 4) (sourceB352 + difference 4 3) sourceC352) = raw6747 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6747; decide +kernel
    rw [ha]
    exact (canonical6747 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA352 + difference 3 5) (sourceB352 + difference 5 3) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2121) := by
    have ha : (tripleCharges (sourceA352 + difference 3 5) (sourceB352 + difference 5 3) sourceC352) = raw7076 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7076; decide +kernel
    rw [ha]
    exact (canonical7076 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA352 + difference 4 0) (sourceB352 + difference 0 4) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA352 + difference 4 0) (sourceB352 + difference 0 4) sourceC352) = raw6403 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6403; decide +kernel
    rw [ha]
    exact (canonical6403 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA352 + difference 4 1) (sourceB352 + difference 1 4) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2679) := by
    have ha : (tripleCharges (sourceA352 + difference 4 1) (sourceB352 + difference 1 4) sourceC352) = raw6404 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6404; decide +kernel
    rw [ha]
    exact (canonical6404 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA352 + difference 4 2) (sourceB352 + difference 2 4) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2699) := by
    have ha : (tripleCharges (sourceA352 + difference 4 2) (sourceB352 + difference 2 4) sourceC352) = raw6405 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6405; decide +kernel
    rw [ha]
    exact (canonical6405 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA352 + difference 4 3) (sourceB352 + difference 3 4) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA352 + difference 4 3) (sourceB352 + difference 3 4) sourceC352) = raw6058 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6058; decide +kernel
    rw [ha]
    exact (canonical6058 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA352 + difference 4 5) (sourceB352 + difference 5 4) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2733) := by
    have ha : (tripleCharges (sourceA352 + difference 4 5) (sourceB352 + difference 5 4) sourceC352) = raw6407 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6407; decide +kernel
    rw [ha]
    exact (canonical6407 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA352 + difference 5 0) (sourceB352 + difference 0 5) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA352 + difference 5 0) (sourceB352 + difference 0 5) sourceC352) = raw6748 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6748; decide +kernel
    rw [ha]
    exact (canonical6748 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA352 + difference 5 1) (sourceB352 + difference 1 5) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA352 + difference 5 1) (sourceB352 + difference 1 5) sourceC352) = raw6749 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6749; decide +kernel
    rw [ha]
    exact (canonical6749 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA352 + difference 5 2) (sourceB352 + difference 2 5) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA352 + difference 5 2) (sourceB352 + difference 2 5) sourceC352) = raw6750 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6750; decide +kernel
    rw [ha]
    exact (canonical6750 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA352 + difference 5 3) (sourceB352 + difference 3 5) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA352 + difference 5 3) (sourceB352 + difference 3 5) sourceC352) = raw6412 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw6412; decide +kernel
    rw [ha]
    exact (canonical6412 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA352 + difference 5 4) (sourceB352 + difference 4 5) sourceC352) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA352 + difference 5 4) (sourceB352 + difference 4 5) sourceC352) = raw7077 := by
      apply Matrix.ext; unfold tripleCharges sourceA352 sourceB352 sourceC352 difference raw7077; decide +kernel
    rw [ha]
    exact (canonical7077 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA352 sourceB352 sourceC352
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm352, Integer.Sparse.eval]
  linarith only [hs]

def sourceA353 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB353 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC353 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm353 : Integer.Sparse Master := [(Sum.inr 2036, 1), (Sum.inr 2037, 1), (Sum.inr 2038, 1), (Sum.inr 2059, 1), (Sum.inr 2254, 1), (Sum.inr 2661, 1), (Sum.inr 2670, 1), (Sum.inr 2672, 1), (Sum.inr 2677, 1), (Sum.inr 2722, 1), (Sum.inr 3015, 1), (Sum.inr 3016, 1), (Sum.inr 3018, 1), (Sum.inr 3028, 1), (Sum.inr 3029, 1), (Sum.inr 3035, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3042, 1), (Sum.inr 3044, 1), (Sum.inr 3052, 1), (Sum.inr 3054, 1), (Sum.inr 3064, 1), (Sum.inr 3086, 1), (Sum.inr 3088, 1), (Sum.inr 3101, 1), (Sum.inr 3196, 1), (Sum.inr 3198, 1), (Sum.inr 3210, 1), (Sum.inr 3224, 1)]

theorem sourceEq353 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm353 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA353 + difference 0 1) (sourceB353 + difference 1 0) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA353 + difference 0 1) (sourceB353 + difference 1 0) sourceC353) = raw7078 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7078; decide +kernel
    rw [ha]
    exact (canonical7078 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA353 + difference 0 2) (sourceB353 + difference 2 0) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA353 + difference 0 2) (sourceB353 + difference 2 0) sourceC353) = raw7079 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7079; decide +kernel
    rw [ha]
    exact (canonical7079 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA353 + difference 0 3) (sourceB353 + difference 3 0) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA353 + difference 0 3) (sourceB353 + difference 3 0) sourceC353) = raw6415 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6415; decide +kernel
    rw [ha]
    exact (canonical6415 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA353 + difference 0 4) (sourceB353 + difference 4 0) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA353 + difference 0 4) (sourceB353 + difference 4 0) sourceC353) = raw6760 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6760; decide +kernel
    rw [ha]
    exact (canonical6760 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA353 + difference 0 5) (sourceB353 + difference 5 0) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA353 + difference 0 5) (sourceB353 + difference 5 0) sourceC353) = raw7080 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7080; decide +kernel
    rw [ha]
    exact (canonical7080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA353 + difference 1 0) (sourceB353 + difference 0 1) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3224) := by
    have ha : (tripleCharges (sourceA353 + difference 1 0) (sourceB353 + difference 0 1) sourceC353) = raw7081 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7081; decide +kernel
    rw [ha]
    exact (canonical7081 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA353 + difference 1 2) (sourceB353 + difference 2 1) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA353 + difference 1 2) (sourceB353 + difference 2 1) sourceC353) = raw7082 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7082; decide +kernel
    rw [ha]
    exact (canonical7082 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA353 + difference 1 3) (sourceB353 + difference 3 1) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA353 + difference 1 3) (sourceB353 + difference 3 1) sourceC353) = raw6419 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6419; decide +kernel
    rw [ha]
    exact (canonical6419 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA353 + difference 1 4) (sourceB353 + difference 4 1) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA353 + difference 1 4) (sourceB353 + difference 4 1) sourceC353) = raw6765 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6765; decide +kernel
    rw [ha]
    exact (canonical6765 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA353 + difference 1 5) (sourceB353 + difference 5 1) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA353 + difference 1 5) (sourceB353 + difference 5 1) sourceC353) = raw7083 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7083; decide +kernel
    rw [ha]
    exact (canonical7083 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA353 + difference 2 0) (sourceB353 + difference 0 2) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA353 + difference 2 0) (sourceB353 + difference 0 2) sourceC353) = raw7084 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7084; decide +kernel
    rw [ha]
    exact (canonical7084 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA353 + difference 2 1) (sourceB353 + difference 1 2) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3018) := by
    have ha : (tripleCharges (sourceA353 + difference 2 1) (sourceB353 + difference 1 2) sourceC353) = raw7085 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7085; decide +kernel
    rw [ha]
    exact (canonical7085 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA353 + difference 2 3) (sourceB353 + difference 3 2) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA353 + difference 2 3) (sourceB353 + difference 3 2) sourceC353) = raw6423 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6423; decide +kernel
    rw [ha]
    exact (canonical6423 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA353 + difference 2 4) (sourceB353 + difference 4 2) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA353 + difference 2 4) (sourceB353 + difference 4 2) sourceC353) = raw6770 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6770; decide +kernel
    rw [ha]
    exact (canonical6770 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA353 + difference 2 5) (sourceB353 + difference 5 2) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3015) := by
    have ha : (tripleCharges (sourceA353 + difference 2 5) (sourceB353 + difference 5 2) sourceC353) = raw7086 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7086; decide +kernel
    rw [ha]
    exact (canonical7086 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA353 + difference 3 0) (sourceB353 + difference 0 3) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA353 + difference 3 0) (sourceB353 + difference 0 3) sourceC353) = raw7087 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7087; decide +kernel
    rw [ha]
    exact (canonical7087 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA353 + difference 3 1) (sourceB353 + difference 1 3) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2038) := by
    have ha : (tripleCharges (sourceA353 + difference 3 1) (sourceB353 + difference 1 3) sourceC353) = raw7088 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7088; decide +kernel
    rw [ha]
    exact (canonical7088 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA353 + difference 3 2) (sourceB353 + difference 2 3) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2036) := by
    have ha : (tripleCharges (sourceA353 + difference 3 2) (sourceB353 + difference 2 3) sourceC353) = raw7089 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7089; decide +kernel
    rw [ha]
    exact (canonical7089 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA353 + difference 3 4) (sourceB353 + difference 4 3) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA353 + difference 3 4) (sourceB353 + difference 4 3) sourceC353) = raw6775 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6775; decide +kernel
    rw [ha]
    exact (canonical6775 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA353 + difference 3 5) (sourceB353 + difference 5 3) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2059) := by
    have ha : (tripleCharges (sourceA353 + difference 3 5) (sourceB353 + difference 5 3) sourceC353) = raw7090 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7090; decide +kernel
    rw [ha]
    exact (canonical7090 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA353 + difference 4 0) (sourceB353 + difference 0 4) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA353 + difference 4 0) (sourceB353 + difference 0 4) sourceC353) = raw6425 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6425; decide +kernel
    rw [ha]
    exact (canonical6425 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA353 + difference 4 1) (sourceB353 + difference 1 4) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3042) := by
    have ha : (tripleCharges (sourceA353 + difference 4 1) (sourceB353 + difference 1 4) sourceC353) = raw6426 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6426; decide +kernel
    rw [ha]
    exact (canonical6426 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA353 + difference 4 2) (sourceB353 + difference 2 4) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3028) := by
    have ha : (tripleCharges (sourceA353 + difference 4 2) (sourceB353 + difference 2 4) sourceC353) = raw6427 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6427; decide +kernel
    rw [ha]
    exact (canonical6427 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA353 + difference 4 3) (sourceB353 + difference 3 4) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA353 + difference 4 3) (sourceB353 + difference 3 4) sourceC353) = raw6088 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6088; decide +kernel
    rw [ha]
    exact (canonical6088 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA353 + difference 4 5) (sourceB353 + difference 5 4) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3035) := by
    have ha : (tripleCharges (sourceA353 + difference 4 5) (sourceB353 + difference 5 4) sourceC353) = raw6429 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6429; decide +kernel
    rw [ha]
    exact (canonical6429 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA353 + difference 5 0) (sourceB353 + difference 0 5) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3210) := by
    have ha : (tripleCharges (sourceA353 + difference 5 0) (sourceB353 + difference 0 5) sourceC353) = raw6776 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6776; decide +kernel
    rw [ha]
    exact (canonical6776 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA353 + difference 5 1) (sourceB353 + difference 1 5) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA353 + difference 5 1) (sourceB353 + difference 1 5) sourceC353) = raw6777 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6777; decide +kernel
    rw [ha]
    exact (canonical6777 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA353 + difference 5 2) (sourceB353 + difference 2 5) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3029) := by
    have ha : (tripleCharges (sourceA353 + difference 5 2) (sourceB353 + difference 2 5) sourceC353) = raw6778 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6778; decide +kernel
    rw [ha]
    exact (canonical6778 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA353 + difference 5 3) (sourceB353 + difference 3 5) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA353 + difference 5 3) (sourceB353 + difference 3 5) sourceC353) = raw6434 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw6434; decide +kernel
    rw [ha]
    exact (canonical6434 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA353 + difference 5 4) (sourceB353 + difference 4 5) sourceC353) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA353 + difference 5 4) (sourceB353 + difference 4 5) sourceC353) = raw7091 := by
      apply Matrix.ext; unfold tripleCharges sourceA353 sourceB353 sourceC353 difference raw7091; decide +kernel
    rw [ha]
    exact (canonical7091 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA353 sourceB353 sourceC353
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm353, Integer.Sparse.eval]
  linarith only [hs]

def sourceA354 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB354 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC354 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm354 : Integer.Sparse Master := [(Sum.inr 2560, 1), (Sum.inr 3375, 1), (Sum.inr 3379, 1), (Sum.inr 3391, 1), (Sum.inr 3533, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem sourceEq354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm354 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA354 + difference 0 0) (sourceB354 + difference 0 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA354 + difference 0 0) (sourceB354 + difference 0 0) sourceC354) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA354 + difference 0 1) (sourceB354 + difference 1 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA354 + difference 0 1) (sourceB354 + difference 1 0) sourceC354) = raw7092 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw7092; decide +kernel
    rw [ha]
    exact (canonical7092 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA354 + difference 0 2) (sourceB354 + difference 2 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3375) := by
    have ha : (tripleCharges (sourceA354 + difference 0 2) (sourceB354 + difference 2 0) sourceC354) = raw7093 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw7093; decide +kernel
    rw [ha]
    exact (canonical7093 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA354 + difference 0 3) (sourceB354 + difference 3 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA354 + difference 0 3) (sourceB354 + difference 3 0) sourceC354) = raw6437 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw6437; decide +kernel
    rw [ha]
    exact (canonical6437 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA354 + difference 0 4) (sourceB354 + difference 4 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA354 + difference 0 4) (sourceB354 + difference 4 0) sourceC354) = raw6789 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw6789; decide +kernel
    rw [ha]
    exact (canonical6789 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA354 + difference 0 5) (sourceB354 + difference 5 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA354 + difference 0 5) (sourceB354 + difference 5 0) sourceC354) = raw7094 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw7094; decide +kernel
    rw [ha]
    exact (canonical7094 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA354 + sourceB354) sourceC354) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA354 + sourceB354) sourceC354) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA354 sourceB354 sourceC354 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA354 sourceB354 sourceC354
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm354, Integer.Sparse.eval]
  linarith only [hs]

def sourceA355 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB355 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC355 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm355 : Integer.Sparse Master := [(Sum.inr 2034, 1), (Sum.inr 2037, 1), (Sum.inr 2039, 1), (Sum.inr 2058, 1), (Sum.inr 2279, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem sourceEq355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm355 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA355 + difference 0 0) (sourceB355 + difference 0 0) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA355 + difference 0 0) (sourceB355 + difference 0 0) sourceC355) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA355 + difference 1 0) (sourceB355 + difference 0 1) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA355 + difference 1 0) (sourceB355 + difference 0 1) sourceC355) = raw7095 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw7095; decide +kernel
    rw [ha]
    exact (canonical7095 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA355 + difference 2 0) (sourceB355 + difference 0 2) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA355 + difference 2 0) (sourceB355 + difference 0 2) sourceC355) = raw7096 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw7096; decide +kernel
    rw [ha]
    exact (canonical7096 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA355 + difference 3 0) (sourceB355 + difference 0 3) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA355 + difference 3 0) (sourceB355 + difference 0 3) sourceC355) = raw7097 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw7097; decide +kernel
    rw [ha]
    exact (canonical7097 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA355 + difference 4 0) (sourceB355 + difference 0 4) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2039) := by
    have ha : (tripleCharges (sourceA355 + difference 4 0) (sourceB355 + difference 0 4) sourceC355) = raw6441 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw6441; decide +kernel
    rw [ha]
    exact (canonical6441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA355 + difference 5 0) (sourceB355 + difference 0 5) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA355 + difference 5 0) (sourceB355 + difference 0 5) sourceC355) = raw6793 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw6793; decide +kernel
    rw [ha]
    exact (canonical6793 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA355 + sourceB355) sourceC355) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA355 + sourceB355) sourceC355) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA355 sourceB355 sourceC355 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA355 sourceB355 sourceC355
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm355, Integer.Sparse.eval]
  linarith only [hs]

def sourceA356 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB356 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC356 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm356 : Integer.Sparse Master := [(Sum.inr 3151, 1), (Sum.inr 3379, 1), (Sum.inr 3382, 1), (Sum.inr 3383, 1), (Sum.inr 3395, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem sourceEq356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm356 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA356 + difference 0 1) (sourceB356 + difference 1 0) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA356 + difference 0 1) (sourceB356 + difference 1 0) sourceC356) = raw7092 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw7092; decide +kernel
    rw [ha]
    exact (canonical7092 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA356 + difference 1 1) (sourceB356 + difference 1 1) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA356 + difference 1 1) (sourceB356 + difference 1 1) sourceC356) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA356 + difference 2 1) (sourceB356 + difference 1 2) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3382) := by
    have ha : (tripleCharges (sourceA356 + difference 2 1) (sourceB356 + difference 1 2) sourceC356) = raw7098 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw7098; decide +kernel
    rw [ha]
    exact (canonical7098 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA356 + difference 3 1) (sourceB356 + difference 1 3) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3151) := by
    have ha : (tripleCharges (sourceA356 + difference 3 1) (sourceB356 + difference 1 3) sourceC356) = raw7099 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw7099; decide +kernel
    rw [ha]
    exact (canonical7099 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA356 + difference 4 1) (sourceB356 + difference 1 4) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3383) := by
    have ha : (tripleCharges (sourceA356 + difference 4 1) (sourceB356 + difference 1 4) sourceC356) = raw6448 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw6448; decide +kernel
    rw [ha]
    exact (canonical6448 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA356 + difference 5 1) (sourceB356 + difference 1 5) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA356 + difference 5 1) (sourceB356 + difference 1 5) sourceC356) = raw6801 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw6801; decide +kernel
    rw [ha]
    exact (canonical6801 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA356 + sourceB356) sourceC356) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA356 + sourceB356) sourceC356) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA356 sourceB356 sourceC356 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA356 sourceB356 sourceC356
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm356, Integer.Sparse.eval]
  linarith only [hs]

def sourceA357 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB357 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC357 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm357 : Integer.Sparse Master := [(Sum.inr 2034, 1), (Sum.inr 2555, 1), (Sum.inr 3382, 1), (Sum.inr 3528, 1), (Sum.inr 3539, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem sourceEq357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm357 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA357 + difference 2 0) (sourceB357 + difference 0 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA357 + difference 2 0) (sourceB357 + difference 0 2) sourceC357) = raw7096 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw7096; decide +kernel
    rw [ha]
    exact (canonical7096 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA357 + difference 2 1) (sourceB357 + difference 1 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3382) := by
    have ha : (tripleCharges (sourceA357 + difference 2 1) (sourceB357 + difference 1 2) sourceC357) = raw7098 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw7098; decide +kernel
    rw [ha]
    exact (canonical7098 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA357 + difference 2 2) (sourceB357 + difference 2 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA357 + difference 2 2) (sourceB357 + difference 2 2) sourceC357) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA357 + difference 2 3) (sourceB357 + difference 3 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA357 + difference 2 3) (sourceB357 + difference 3 2) sourceC357) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA357 + difference 2 4) (sourceB357 + difference 4 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA357 + difference 2 4) (sourceB357 + difference 4 2) sourceC357) = raw6805 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw6805; decide +kernel
    rw [ha]
    exact (canonical6805 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA357 + difference 2 5) (sourceB357 + difference 5 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2555) := by
    have ha : (tripleCharges (sourceA357 + difference 2 5) (sourceB357 + difference 5 2) sourceC357) = raw7100 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw7100; decide +kernel
    rw [ha]
    exact (canonical7100 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA357 + sourceB357) sourceC357) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA357 + sourceB357) sourceC357) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA357 sourceB357 sourceC357 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA357 sourceB357 sourceC357
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm357, Integer.Sparse.eval]
  linarith only [hs]

def sourceA358 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB358 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC358 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm358 : Integer.Sparse Master := [(Sum.inr 3148, 1), (Sum.inr 3375, 1), (Sum.inr 3490, 1), (Sum.inr 3497, 1), (Sum.inr 3541, 2), (Sum.inr 4084, -1)]

theorem sourceEq358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm358 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA358 + difference 0 2) (sourceB358 + difference 2 0) sourceC358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3375) := by
    have ha : (tripleCharges (sourceA358 + difference 0 2) (sourceB358 + difference 2 0) sourceC358) = raw7093 := by
      apply Matrix.ext; unfold tripleCharges sourceA358 sourceB358 sourceC358 difference raw7093; decide +kernel
    rw [ha]
    exact (canonical7093 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA358 + difference 1 2) (sourceB358 + difference 2 1) sourceC358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA358 + difference 1 2) (sourceB358 + difference 2 1) sourceC358) = raw7101 := by
      apply Matrix.ext; unfold tripleCharges sourceA358 sourceB358 sourceC358 difference raw7101; decide +kernel
    rw [ha]
    exact (canonical7101 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA358 + difference 2 2) (sourceB358 + difference 2 2) sourceC358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA358 + difference 2 2) (sourceB358 + difference 2 2) sourceC358) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA358 sourceB358 sourceC358 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA358 + difference 3 2) (sourceB358 + difference 2 3) sourceC358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3148) := by
    have ha : (tripleCharges (sourceA358 + difference 3 2) (sourceB358 + difference 2 3) sourceC358) = raw7102 := by
      apply Matrix.ext; unfold tripleCharges sourceA358 sourceB358 sourceC358 difference raw7102; decide +kernel
    rw [ha]
    exact (canonical7102 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA358 + difference 4 2) (sourceB358 + difference 2 4) sourceC358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3490) := by
    have ha : (tripleCharges (sourceA358 + difference 4 2) (sourceB358 + difference 2 4) sourceC358) = raw6452 := by
      apply Matrix.ext; unfold tripleCharges sourceA358 sourceB358 sourceC358 difference raw6452; decide +kernel
    rw [ha]
    exact (canonical6452 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA358 + difference 5 2) (sourceB358 + difference 2 5) sourceC358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA358 + difference 5 2) (sourceB358 + difference 2 5) sourceC358) = raw6807 := by
      apply Matrix.ext; unfold tripleCharges sourceA358 sourceB358 sourceC358 difference raw6807; decide +kernel
    rw [ha]
    exact (canonical6807 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA358 + sourceB358) sourceC358) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA358 + sourceB358) sourceC358) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA358 sourceB358 sourceC358 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA358 sourceB358 sourceC358
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm358, Integer.Sparse.eval]
  linarith only [hs]

def sourceA359 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB359 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC359 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm359 : Integer.Sparse Master := [(Sum.inr 4577, 1), (Sum.inr 4578, 1), (Sum.inr 4582, 1), (Sum.inr 4590, 2), (Sum.inr 5048, 2), (Sum.inr 5065, 1), (Sum.inr 5067, 1), (Sum.inr 5073, 2), (Sum.inr 5182, 2), (Sum.inr 5185, 2), (Sum.inr 5190, 2), (Sum.inr 5251, 1), (Sum.inr 5252, 1), (Sum.inr 5257, 2), (Sum.inr 5259, 2), (Sum.inr 5281, 1), (Sum.inr 5282, 1), (Sum.inr 5405, 1), (Sum.inr 5430, 2), (Sum.inr 5433, 1), (Sum.inr 5439, 1)]

theorem sourceEq359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm359 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA359 + difference 0 1) (sourceB359 + difference 1 0) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA359 + difference 0 1) (sourceB359 + difference 1 0) sourceC359) = raw7103 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7103; decide +kernel
    rw [ha]
    exact (canonical7103 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA359 + difference 0 2) (sourceB359 + difference 2 0) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA359 + difference 0 2) (sourceB359 + difference 2 0) sourceC359) = raw7104 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7104; decide +kernel
    rw [ha]
    exact (canonical7104 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA359 + difference 0 3) (sourceB359 + difference 3 0) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA359 + difference 0 3) (sourceB359 + difference 3 0) sourceC359) = raw7105 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7105; decide +kernel
    rw [ha]
    exact (canonical7105 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA359 + difference 0 4) (sourceB359 + difference 4 0) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA359 + difference 0 4) (sourceB359 + difference 4 0) sourceC359) = raw7106 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7106; decide +kernel
    rw [ha]
    exact (canonical7106 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA359 + difference 0 5) (sourceB359 + difference 5 0) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA359 + difference 0 5) (sourceB359 + difference 5 0) sourceC359) = raw7107 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7107; decide +kernel
    rw [ha]
    exact (canonical7107 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA359 + difference 1 0) (sourceB359 + difference 0 1) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4582) := by
    have ha : (tripleCharges (sourceA359 + difference 1 0) (sourceB359 + difference 0 1) sourceC359) = raw7108 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7108; decide +kernel
    rw [ha]
    exact (canonical7108 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA359 + difference 1 2) (sourceB359 + difference 2 1) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5190) := by
    have ha : (tripleCharges (sourceA359 + difference 1 2) (sourceB359 + difference 2 1) sourceC359) = raw7109 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7109; decide +kernel
    rw [ha]
    exact (canonical7109 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA359 + difference 1 3) (sourceB359 + difference 3 1) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5190) := by
    have ha : (tripleCharges (sourceA359 + difference 1 3) (sourceB359 + difference 3 1) sourceC359) = raw7110 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7110; decide +kernel
    rw [ha]
    exact (canonical7110 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA359 + difference 1 4) (sourceB359 + difference 4 1) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA359 + difference 1 4) (sourceB359 + difference 4 1) sourceC359) = raw7111 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7111; decide +kernel
    rw [ha]
    exact (canonical7111 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA359 + difference 1 5) (sourceB359 + difference 5 1) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA359 + difference 1 5) (sourceB359 + difference 5 1) sourceC359) = raw7112 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7112; decide +kernel
    rw [ha]
    exact (canonical7112 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA359 + difference 2 0) (sourceB359 + difference 0 2) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA359 + difference 2 0) (sourceB359 + difference 0 2) sourceC359) = raw7113 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7113; decide +kernel
    rw [ha]
    exact (canonical7113 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA359 + difference 2 1) (sourceB359 + difference 1 2) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA359 + difference 2 1) (sourceB359 + difference 1 2) sourceC359) = raw7114 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7114; decide +kernel
    rw [ha]
    exact (canonical7114 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA359 + difference 2 3) (sourceB359 + difference 3 2) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA359 + difference 2 3) (sourceB359 + difference 3 2) sourceC359) = raw7115 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7115; decide +kernel
    rw [ha]
    exact (canonical7115 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA359 + difference 2 4) (sourceB359 + difference 4 2) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA359 + difference 2 4) (sourceB359 + difference 4 2) sourceC359) = raw7116 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7116; decide +kernel
    rw [ha]
    exact (canonical7116 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA359 + difference 2 5) (sourceB359 + difference 5 2) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA359 + difference 2 5) (sourceB359 + difference 5 2) sourceC359) = raw7117 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7117; decide +kernel
    rw [ha]
    exact (canonical7117 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA359 + difference 3 0) (sourceB359 + difference 0 3) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA359 + difference 3 0) (sourceB359 + difference 0 3) sourceC359) = raw7118 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7118; decide +kernel
    rw [ha]
    exact (canonical7118 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA359 + difference 3 1) (sourceB359 + difference 1 3) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA359 + difference 3 1) (sourceB359 + difference 1 3) sourceC359) = raw7119 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7119; decide +kernel
    rw [ha]
    exact (canonical7119 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA359 + difference 3 2) (sourceB359 + difference 2 3) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA359 + difference 3 2) (sourceB359 + difference 2 3) sourceC359) = raw7120 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7120; decide +kernel
    rw [ha]
    exact (canonical7120 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA359 + difference 3 4) (sourceB359 + difference 4 3) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA359 + difference 3 4) (sourceB359 + difference 4 3) sourceC359) = raw7121 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7121; decide +kernel
    rw [ha]
    exact (canonical7121 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA359 + difference 3 5) (sourceB359 + difference 5 3) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA359 + difference 3 5) (sourceB359 + difference 5 3) sourceC359) = raw7122 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7122; decide +kernel
    rw [ha]
    exact (canonical7122 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA359 + difference 4 0) (sourceB359 + difference 0 4) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4578) := by
    have ha : (tripleCharges (sourceA359 + difference 4 0) (sourceB359 + difference 0 4) sourceC359) = raw7123 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7123; decide +kernel
    rw [ha]
    exact (canonical7123 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA359 + difference 4 1) (sourceB359 + difference 1 4) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA359 + difference 4 1) (sourceB359 + difference 1 4) sourceC359) = raw7124 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7124; decide +kernel
    rw [ha]
    exact (canonical7124 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA359 + difference 4 2) (sourceB359 + difference 2 4) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5182) := by
    have ha : (tripleCharges (sourceA359 + difference 4 2) (sourceB359 + difference 2 4) sourceC359) = raw7125 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7125; decide +kernel
    rw [ha]
    exact (canonical7125 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA359 + difference 4 3) (sourceB359 + difference 3 4) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5182) := by
    have ha : (tripleCharges (sourceA359 + difference 4 3) (sourceB359 + difference 3 4) sourceC359) = raw7126 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7126; decide +kernel
    rw [ha]
    exact (canonical7126 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA359 + difference 4 5) (sourceB359 + difference 5 4) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA359 + difference 4 5) (sourceB359 + difference 5 4) sourceC359) = raw7127 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7127; decide +kernel
    rw [ha]
    exact (canonical7127 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA359 + difference 5 0) (sourceB359 + difference 0 5) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4577) := by
    have ha : (tripleCharges (sourceA359 + difference 5 0) (sourceB359 + difference 0 5) sourceC359) = raw7128 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7128; decide +kernel
    rw [ha]
    exact (canonical7128 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA359 + difference 5 1) (sourceB359 + difference 1 5) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5065) := by
    have ha : (tripleCharges (sourceA359 + difference 5 1) (sourceB359 + difference 1 5) sourceC359) = raw7129 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7129; decide +kernel
    rw [ha]
    exact (canonical7129 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA359 + difference 5 2) (sourceB359 + difference 2 5) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5048) := by
    have ha : (tripleCharges (sourceA359 + difference 5 2) (sourceB359 + difference 2 5) sourceC359) = raw7130 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7130; decide +kernel
    rw [ha]
    exact (canonical7130 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA359 + difference 5 3) (sourceB359 + difference 3 5) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5048) := by
    have ha : (tripleCharges (sourceA359 + difference 5 3) (sourceB359 + difference 3 5) sourceC359) = raw7131 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7131; decide +kernel
    rw [ha]
    exact (canonical7131 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA359 + difference 5 4) (sourceB359 + difference 4 5) sourceC359) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA359 + difference 5 4) (sourceB359 + difference 4 5) sourceC359) = raw7132 := by
      apply Matrix.ext; unfold tripleCharges sourceA359 sourceB359 sourceC359 difference raw7132; decide +kernel
    rw [ha]
    exact (canonical7132 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA359 sourceB359 sourceC359
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm359, Integer.Sparse.eval]
  linarith only [hs]

def sourceA360 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB360 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC360 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm360 : Integer.Sparse Master := [(Sum.inr 1195, 1), (Sum.inr 1196, 1), (Sum.inr 1201, 1), (Sum.inr 1213, 2), (Sum.inr 2450, 2), (Sum.inr 2470, 1), (Sum.inr 2712, 1), (Sum.inr 2850, 2), (Sum.inr 2854, 2), (Sum.inr 2862, 2), (Sum.inr 2981, 1), (Sum.inr 2987, 2), (Sum.inr 3064, 1), (Sum.inr 3074, 1), (Sum.inr 3078, 1), (Sum.inr 3087, 2), (Sum.inr 3088, 2), (Sum.inr 3972, 2), (Sum.inr 3977, 1), (Sum.inr 4012, 1), (Sum.inr 4033, 1)]

theorem sourceEq360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm360 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA360 + difference 0 1) (sourceB360 + difference 1 0) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA360 + difference 0 1) (sourceB360 + difference 1 0) sourceC360) = raw7133 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7133; decide +kernel
    rw [ha]
    exact (canonical7133 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA360 + difference 0 2) (sourceB360 + difference 2 0) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA360 + difference 0 2) (sourceB360 + difference 2 0) sourceC360) = raw7134 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7134; decide +kernel
    rw [ha]
    exact (canonical7134 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA360 + difference 0 3) (sourceB360 + difference 3 0) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA360 + difference 0 3) (sourceB360 + difference 3 0) sourceC360) = raw7135 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7135; decide +kernel
    rw [ha]
    exact (canonical7135 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA360 + difference 0 4) (sourceB360 + difference 4 0) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA360 + difference 0 4) (sourceB360 + difference 4 0) sourceC360) = raw7136 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7136; decide +kernel
    rw [ha]
    exact (canonical7136 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA360 + difference 0 5) (sourceB360 + difference 5 0) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA360 + difference 0 5) (sourceB360 + difference 5 0) sourceC360) = raw7137 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7137; decide +kernel
    rw [ha]
    exact (canonical7137 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA360 + difference 1 0) (sourceB360 + difference 0 1) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1201) := by
    have ha : (tripleCharges (sourceA360 + difference 1 0) (sourceB360 + difference 0 1) sourceC360) = raw7138 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7138; decide +kernel
    rw [ha]
    exact (canonical7138 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA360 + difference 1 2) (sourceB360 + difference 2 1) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2854) := by
    have ha : (tripleCharges (sourceA360 + difference 1 2) (sourceB360 + difference 2 1) sourceC360) = raw7139 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7139; decide +kernel
    rw [ha]
    exact (canonical7139 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA360 + difference 1 3) (sourceB360 + difference 3 1) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2854) := by
    have ha : (tripleCharges (sourceA360 + difference 1 3) (sourceB360 + difference 3 1) sourceC360) = raw7140 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7140; decide +kernel
    rw [ha]
    exact (canonical7140 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA360 + difference 1 4) (sourceB360 + difference 4 1) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA360 + difference 1 4) (sourceB360 + difference 4 1) sourceC360) = raw7141 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7141; decide +kernel
    rw [ha]
    exact (canonical7141 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA360 + difference 1 5) (sourceB360 + difference 5 1) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA360 + difference 1 5) (sourceB360 + difference 5 1) sourceC360) = raw7142 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7142; decide +kernel
    rw [ha]
    exact (canonical7142 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA360 + difference 2 0) (sourceB360 + difference 0 2) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA360 + difference 2 0) (sourceB360 + difference 0 2) sourceC360) = raw7143 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7143; decide +kernel
    rw [ha]
    exact (canonical7143 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA360 + difference 2 1) (sourceB360 + difference 1 2) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2987) := by
    have ha : (tripleCharges (sourceA360 + difference 2 1) (sourceB360 + difference 1 2) sourceC360) = raw7144 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7144; decide +kernel
    rw [ha]
    exact (canonical7144 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA360 + difference 2 3) (sourceB360 + difference 3 2) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA360 + difference 2 3) (sourceB360 + difference 3 2) sourceC360) = raw7145 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7145; decide +kernel
    rw [ha]
    exact (canonical7145 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA360 + difference 2 4) (sourceB360 + difference 4 2) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA360 + difference 2 4) (sourceB360 + difference 4 2) sourceC360) = raw7146 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7146; decide +kernel
    rw [ha]
    exact (canonical7146 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA360 + difference 2 5) (sourceB360 + difference 5 2) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA360 + difference 2 5) (sourceB360 + difference 5 2) sourceC360) = raw7147 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7147; decide +kernel
    rw [ha]
    exact (canonical7147 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA360 + difference 3 0) (sourceB360 + difference 0 3) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA360 + difference 3 0) (sourceB360 + difference 0 3) sourceC360) = raw7148 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7148; decide +kernel
    rw [ha]
    exact (canonical7148 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA360 + difference 3 1) (sourceB360 + difference 1 3) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2987) := by
    have ha : (tripleCharges (sourceA360 + difference 3 1) (sourceB360 + difference 1 3) sourceC360) = raw7149 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7149; decide +kernel
    rw [ha]
    exact (canonical7149 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA360 + difference 3 2) (sourceB360 + difference 2 3) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA360 + difference 3 2) (sourceB360 + difference 2 3) sourceC360) = raw7150 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7150; decide +kernel
    rw [ha]
    exact (canonical7150 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA360 + difference 3 4) (sourceB360 + difference 4 3) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA360 + difference 3 4) (sourceB360 + difference 4 3) sourceC360) = raw7151 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7151; decide +kernel
    rw [ha]
    exact (canonical7151 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA360 + difference 3 5) (sourceB360 + difference 5 3) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA360 + difference 3 5) (sourceB360 + difference 5 3) sourceC360) = raw7152 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7152; decide +kernel
    rw [ha]
    exact (canonical7152 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA360 + difference 4 0) (sourceB360 + difference 0 4) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1196) := by
    have ha : (tripleCharges (sourceA360 + difference 4 0) (sourceB360 + difference 0 4) sourceC360) = raw7153 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7153; decide +kernel
    rw [ha]
    exact (canonical7153 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA360 + difference 4 1) (sourceB360 + difference 1 4) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA360 + difference 4 1) (sourceB360 + difference 1 4) sourceC360) = raw7154 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7154; decide +kernel
    rw [ha]
    exact (canonical7154 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA360 + difference 4 2) (sourceB360 + difference 2 4) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2850) := by
    have ha : (tripleCharges (sourceA360 + difference 4 2) (sourceB360 + difference 2 4) sourceC360) = raw7155 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7155; decide +kernel
    rw [ha]
    exact (canonical7155 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA360 + difference 4 3) (sourceB360 + difference 3 4) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2850) := by
    have ha : (tripleCharges (sourceA360 + difference 4 3) (sourceB360 + difference 3 4) sourceC360) = raw7156 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7156; decide +kernel
    rw [ha]
    exact (canonical7156 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA360 + difference 4 5) (sourceB360 + difference 5 4) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA360 + difference 4 5) (sourceB360 + difference 5 4) sourceC360) = raw7157 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7157; decide +kernel
    rw [ha]
    exact (canonical7157 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA360 + difference 5 0) (sourceB360 + difference 0 5) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1195) := by
    have ha : (tripleCharges (sourceA360 + difference 5 0) (sourceB360 + difference 0 5) sourceC360) = raw7158 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7158; decide +kernel
    rw [ha]
    exact (canonical7158 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA360 + difference 5 1) (sourceB360 + difference 1 5) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA360 + difference 5 1) (sourceB360 + difference 1 5) sourceC360) = raw7159 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7159; decide +kernel
    rw [ha]
    exact (canonical7159 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA360 + difference 5 2) (sourceB360 + difference 2 5) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2450) := by
    have ha : (tripleCharges (sourceA360 + difference 5 2) (sourceB360 + difference 2 5) sourceC360) = raw7160 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7160; decide +kernel
    rw [ha]
    exact (canonical7160 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA360 + difference 5 3) (sourceB360 + difference 3 5) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2450) := by
    have ha : (tripleCharges (sourceA360 + difference 5 3) (sourceB360 + difference 3 5) sourceC360) = raw7161 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7161; decide +kernel
    rw [ha]
    exact (canonical7161 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA360 + difference 5 4) (sourceB360 + difference 4 5) sourceC360) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA360 + difference 5 4) (sourceB360 + difference 4 5) sourceC360) = raw7162 := by
      apply Matrix.ext; unfold tripleCharges sourceA360 sourceB360 sourceC360 difference raw7162; decide +kernel
    rw [ha]
    exact (canonical7162 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA360 sourceB360 sourceC360
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm360, Integer.Sparse.eval]
  linarith only [hs]

def sourceA361 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB361 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC361 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm361 : Integer.Sparse Master := [(Sum.inr 3279, 1), (Sum.inr 3280, 1), (Sum.inr 3282, 1), (Sum.inr 3290, 2), (Sum.inr 3434, 2), (Sum.inr 3466, 1), (Sum.inr 3467, 2), (Sum.inr 3476, 1), (Sum.inr 3529, 2), (Sum.inr 3532, 2), (Sum.inr 3536, 2), (Sum.inr 3539, 1), (Sum.inr 3543, 1), (Sum.inr 3544, 2), (Sum.inr 3568, 2), (Sum.inr 3571, 1), (Sum.inr 3580, 1), (Sum.inr 3805, 1), (Sum.inr 3848, 2), (Sum.inr 3851, 1), (Sum.inr 3858, 1)]

theorem sourceEq361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm361 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA361 + difference 0 1) (sourceB361 + difference 1 0) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA361 + difference 0 1) (sourceB361 + difference 1 0) sourceC361) = raw7163 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7163; decide +kernel
    rw [ha]
    exact (canonical7163 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA361 + difference 0 2) (sourceB361 + difference 2 0) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA361 + difference 0 2) (sourceB361 + difference 2 0) sourceC361) = raw7164 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7164; decide +kernel
    rw [ha]
    exact (canonical7164 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA361 + difference 0 3) (sourceB361 + difference 3 0) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA361 + difference 0 3) (sourceB361 + difference 3 0) sourceC361) = raw7165 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7165; decide +kernel
    rw [ha]
    exact (canonical7165 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA361 + difference 0 4) (sourceB361 + difference 4 0) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA361 + difference 0 4) (sourceB361 + difference 4 0) sourceC361) = raw7166 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7166; decide +kernel
    rw [ha]
    exact (canonical7166 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA361 + difference 0 5) (sourceB361 + difference 5 0) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA361 + difference 0 5) (sourceB361 + difference 5 0) sourceC361) = raw7167 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7167; decide +kernel
    rw [ha]
    exact (canonical7167 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA361 + difference 1 0) (sourceB361 + difference 0 1) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3282) := by
    have ha : (tripleCharges (sourceA361 + difference 1 0) (sourceB361 + difference 0 1) sourceC361) = raw7168 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7168; decide +kernel
    rw [ha]
    exact (canonical7168 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA361 + difference 1 2) (sourceB361 + difference 2 1) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3568) := by
    have ha : (tripleCharges (sourceA361 + difference 1 2) (sourceB361 + difference 2 1) sourceC361) = raw7169 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7169; decide +kernel
    rw [ha]
    exact (canonical7169 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA361 + difference 1 3) (sourceB361 + difference 3 1) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3568) := by
    have ha : (tripleCharges (sourceA361 + difference 1 3) (sourceB361 + difference 3 1) sourceC361) = raw7170 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7170; decide +kernel
    rw [ha]
    exact (canonical7170 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA361 + difference 1 4) (sourceB361 + difference 4 1) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA361 + difference 1 4) (sourceB361 + difference 4 1) sourceC361) = raw7171 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7171; decide +kernel
    rw [ha]
    exact (canonical7171 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA361 + difference 1 5) (sourceB361 + difference 5 1) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA361 + difference 1 5) (sourceB361 + difference 5 1) sourceC361) = raw7172 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7172; decide +kernel
    rw [ha]
    exact (canonical7172 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA361 + difference 2 0) (sourceB361 + difference 0 2) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA361 + difference 2 0) (sourceB361 + difference 0 2) sourceC361) = raw7173 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7173; decide +kernel
    rw [ha]
    exact (canonical7173 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA361 + difference 2 1) (sourceB361 + difference 1 2) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA361 + difference 2 1) (sourceB361 + difference 1 2) sourceC361) = raw7174 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7174; decide +kernel
    rw [ha]
    exact (canonical7174 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA361 + difference 2 3) (sourceB361 + difference 3 2) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA361 + difference 2 3) (sourceB361 + difference 3 2) sourceC361) = raw7175 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7175; decide +kernel
    rw [ha]
    exact (canonical7175 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA361 + difference 2 4) (sourceB361 + difference 4 2) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA361 + difference 2 4) (sourceB361 + difference 4 2) sourceC361) = raw7176 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7176; decide +kernel
    rw [ha]
    exact (canonical7176 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA361 + difference 2 5) (sourceB361 + difference 5 2) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA361 + difference 2 5) (sourceB361 + difference 5 2) sourceC361) = raw7177 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7177; decide +kernel
    rw [ha]
    exact (canonical7177 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA361 + difference 3 0) (sourceB361 + difference 0 3) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA361 + difference 3 0) (sourceB361 + difference 0 3) sourceC361) = raw7178 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7178; decide +kernel
    rw [ha]
    exact (canonical7178 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA361 + difference 3 1) (sourceB361 + difference 1 3) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA361 + difference 3 1) (sourceB361 + difference 1 3) sourceC361) = raw7179 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7179; decide +kernel
    rw [ha]
    exact (canonical7179 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA361 + difference 3 2) (sourceB361 + difference 2 3) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA361 + difference 3 2) (sourceB361 + difference 2 3) sourceC361) = raw7180 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7180; decide +kernel
    rw [ha]
    exact (canonical7180 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA361 + difference 3 4) (sourceB361 + difference 4 3) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA361 + difference 3 4) (sourceB361 + difference 4 3) sourceC361) = raw7181 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7181; decide +kernel
    rw [ha]
    exact (canonical7181 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA361 + difference 3 5) (sourceB361 + difference 5 3) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA361 + difference 3 5) (sourceB361 + difference 5 3) sourceC361) = raw7182 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7182; decide +kernel
    rw [ha]
    exact (canonical7182 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA361 + difference 4 0) (sourceB361 + difference 0 4) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3280) := by
    have ha : (tripleCharges (sourceA361 + difference 4 0) (sourceB361 + difference 0 4) sourceC361) = raw7183 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7183; decide +kernel
    rw [ha]
    exact (canonical7183 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA361 + difference 4 1) (sourceB361 + difference 1 4) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA361 + difference 4 1) (sourceB361 + difference 1 4) sourceC361) = raw7184 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7184; decide +kernel
    rw [ha]
    exact (canonical7184 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA361 + difference 4 2) (sourceB361 + difference 2 4) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3536) := by
    have ha : (tripleCharges (sourceA361 + difference 4 2) (sourceB361 + difference 2 4) sourceC361) = raw7185 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7185; decide +kernel
    rw [ha]
    exact (canonical7185 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA361 + difference 4 3) (sourceB361 + difference 3 4) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3536) := by
    have ha : (tripleCharges (sourceA361 + difference 4 3) (sourceB361 + difference 3 4) sourceC361) = raw7186 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7186; decide +kernel
    rw [ha]
    exact (canonical7186 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA361 + difference 4 5) (sourceB361 + difference 5 4) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA361 + difference 4 5) (sourceB361 + difference 5 4) sourceC361) = raw7187 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7187; decide +kernel
    rw [ha]
    exact (canonical7187 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA361 + difference 5 0) (sourceB361 + difference 0 5) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3279) := by
    have ha : (tripleCharges (sourceA361 + difference 5 0) (sourceB361 + difference 0 5) sourceC361) = raw7188 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7188; decide +kernel
    rw [ha]
    exact (canonical7188 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA361 + difference 5 1) (sourceB361 + difference 1 5) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA361 + difference 5 1) (sourceB361 + difference 1 5) sourceC361) = raw7189 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7189; decide +kernel
    rw [ha]
    exact (canonical7189 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA361 + difference 5 2) (sourceB361 + difference 2 5) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3434) := by
    have ha : (tripleCharges (sourceA361 + difference 5 2) (sourceB361 + difference 2 5) sourceC361) = raw7190 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7190; decide +kernel
    rw [ha]
    exact (canonical7190 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA361 + difference 5 3) (sourceB361 + difference 3 5) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3434) := by
    have ha : (tripleCharges (sourceA361 + difference 5 3) (sourceB361 + difference 3 5) sourceC361) = raw7191 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7191; decide +kernel
    rw [ha]
    exact (canonical7191 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA361 + difference 5 4) (sourceB361 + difference 4 5) sourceC361) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA361 + difference 5 4) (sourceB361 + difference 4 5) sourceC361) = raw7192 := by
      apply Matrix.ext; unfold tripleCharges sourceA361 sourceB361 sourceC361 difference raw7192; decide +kernel
    rw [ha]
    exact (canonical7192 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA361 sourceB361 sourceC361
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm361, Integer.Sparse.eval]
  linarith only [hs]

def sourceA362 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB362 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC362 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm362 : Integer.Sparse Master := [(Sum.inr 2709, 1), (Sum.inr 3800, 1), (Sum.inr 3871, 2), (Sum.inr 3901, 1), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

theorem sourceEq362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm362 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA362 + difference 0 0) (sourceB362 + difference 0 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA362 + difference 0 0) (sourceB362 + difference 0 0) sourceC362) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA362 + difference 0 1) (sourceB362 + difference 1 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA362 + difference 0 1) (sourceB362 + difference 1 0) sourceC362) = raw7194 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7194; decide +kernel
    rw [ha]
    exact (canonical7194 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA362 + difference 0 2) (sourceB362 + difference 2 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA362 + difference 0 2) (sourceB362 + difference 2 0) sourceC362) = raw7195 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7195; decide +kernel
    rw [ha]
    exact (canonical7195 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA362 + difference 0 3) (sourceB362 + difference 3 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA362 + difference 0 3) (sourceB362 + difference 3 0) sourceC362) = raw7196 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7196; decide +kernel
    rw [ha]
    exact (canonical7196 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA362 + difference 0 4) (sourceB362 + difference 4 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA362 + difference 0 4) (sourceB362 + difference 4 0) sourceC362) = raw7197 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7197; decide +kernel
    rw [ha]
    exact (canonical7197 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA362 + difference 0 5) (sourceB362 + difference 5 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3901) := by
    have ha : (tripleCharges (sourceA362 + difference 0 5) (sourceB362 + difference 5 0) sourceC362) = raw7198 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7198; decide +kernel
    rw [ha]
    exact (canonical7198 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA362 + sourceB362) sourceC362) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA362 + sourceB362) sourceC362) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA362 sourceB362 sourceC362 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA362 sourceB362 sourceC362
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm362, Integer.Sparse.eval]
  linarith only [hs]

def sourceA363 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB363 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC363 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm363 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 1208, 1), (Sum.inr 1213, 2), (Sum.inr 1247, 1), (Sum.inr 2709, 1), (Sum.inr 4091, -1)]

theorem sourceEq363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm363 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA363 + difference 0 0) (sourceB363 + difference 0 0) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA363 + difference 0 0) (sourceB363 + difference 0 0) sourceC363) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA363 + difference 1 0) (sourceB363 + difference 0 1) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1247) := by
    have ha : (tripleCharges (sourceA363 + difference 1 0) (sourceB363 + difference 0 1) sourceC363) = raw7200 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7200; decide +kernel
    rw [ha]
    exact (canonical7200 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA363 + difference 2 0) (sourceB363 + difference 0 2) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA363 + difference 2 0) (sourceB363 + difference 0 2) sourceC363) = raw7201 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7201; decide +kernel
    rw [ha]
    exact (canonical7201 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA363 + difference 3 0) (sourceB363 + difference 0 3) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA363 + difference 3 0) (sourceB363 + difference 0 3) sourceC363) = raw7202 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7202; decide +kernel
    rw [ha]
    exact (canonical7202 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA363 + difference 4 0) (sourceB363 + difference 0 4) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1208) := by
    have ha : (tripleCharges (sourceA363 + difference 4 0) (sourceB363 + difference 0 4) sourceC363) = raw7203 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7203; decide +kernel
    rw [ha]
    exact (canonical7203 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA363 + difference 5 0) (sourceB363 + difference 0 5) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1206) := by
    have ha : (tripleCharges (sourceA363 + difference 5 0) (sourceB363 + difference 0 5) sourceC363) = raw7204 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7204; decide +kernel
    rw [ha]
    exact (canonical7204 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA363 + sourceB363) sourceC363) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA363 + sourceB363) sourceC363) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA363 sourceB363 sourceC363 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA363 sourceB363 sourceC363
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm363, Integer.Sparse.eval]
  linarith only [hs]

def sourceA364 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB364 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC364 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm364 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 2622, 2), (Sum.inr 2709, 1), (Sum.inr 2750, 1), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

theorem sourceEq364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm364 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA364 + difference 1 0) (sourceB364 + difference 0 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1247) := by
    have ha : (tripleCharges (sourceA364 + difference 1 0) (sourceB364 + difference 0 1) sourceC364) = raw7200 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7200; decide +kernel
    rw [ha]
    exact (canonical7200 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA364 + difference 1 1) (sourceB364 + difference 1 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA364 + difference 1 1) (sourceB364 + difference 1 1) sourceC364) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA364 + difference 1 2) (sourceB364 + difference 2 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2622) := by
    have ha : (tripleCharges (sourceA364 + difference 1 2) (sourceB364 + difference 2 1) sourceC364) = raw7205 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7205; decide +kernel
    rw [ha]
    exact (canonical7205 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA364 + difference 1 3) (sourceB364 + difference 3 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2622) := by
    have ha : (tripleCharges (sourceA364 + difference 1 3) (sourceB364 + difference 3 1) sourceC364) = raw7206 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7206; decide +kernel
    rw [ha]
    exact (canonical7206 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA364 + difference 1 4) (sourceB364 + difference 4 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA364 + difference 1 4) (sourceB364 + difference 4 1) sourceC364) = raw7207 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7207; decide +kernel
    rw [ha]
    exact (canonical7207 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA364 + difference 1 5) (sourceB364 + difference 5 1) sourceC364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA364 + difference 1 5) (sourceB364 + difference 5 1) sourceC364) = raw7208 := by
      apply Matrix.ext; unfold tripleCharges sourceA364 sourceB364 sourceC364 difference raw7208; decide +kernel
    rw [ha]
    exact (canonical7208 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA364 + sourceB364) sourceC364) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA364 + sourceB364) sourceC364) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA364 sourceB364 sourceC364 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA364 sourceB364 sourceC364
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm364, Integer.Sparse.eval]
  linarith only [hs]

def sourceA365 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB365 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC365 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm365 : Integer.Sparse Master := [(Sum.inr 2470, 1), (Sum.inr 2473, 1), (Sum.inr 2480, 2), (Sum.inr 2709, 1), (Sum.inr 3800, 1), (Sum.inr 4091, -1)]

theorem sourceEq365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm365 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA365 + difference 0 1) (sourceB365 + difference 1 0) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA365 + difference 0 1) (sourceB365 + difference 1 0) sourceC365) = raw7194 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7194; decide +kernel
    rw [ha]
    exact (canonical7194 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA365 + difference 1 1) (sourceB365 + difference 1 1) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA365 + difference 1 1) (sourceB365 + difference 1 1) sourceC365) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA365 + difference 2 1) (sourceB365 + difference 1 2) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA365 + difference 2 1) (sourceB365 + difference 1 2) sourceC365) = raw7209 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7209; decide +kernel
    rw [ha]
    exact (canonical7209 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA365 + difference 3 1) (sourceB365 + difference 1 3) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA365 + difference 3 1) (sourceB365 + difference 1 3) sourceC365) = raw7210 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7210; decide +kernel
    rw [ha]
    exact (canonical7210 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA365 + difference 4 1) (sourceB365 + difference 1 4) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA365 + difference 4 1) (sourceB365 + difference 1 4) sourceC365) = raw7211 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7211; decide +kernel
    rw [ha]
    exact (canonical7211 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA365 + difference 5 1) (sourceB365 + difference 1 5) sourceC365) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA365 + difference 5 1) (sourceB365 + difference 1 5) sourceC365) = raw7212 := by
      apply Matrix.ext; unfold tripleCharges sourceA365 sourceB365 sourceC365 difference raw7212; decide +kernel
    rw [ha]
    exact (canonical7212 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA365 + sourceB365) sourceC365) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA365 + sourceB365) sourceC365) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA365 sourceB365 sourceC365 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA365 sourceB365 sourceC365
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm365, Integer.Sparse.eval]
  linarith only [hs]

def sourceA366 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB366 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC366 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm366 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 2480, 1), (Sum.inr 2615, 1), (Sum.inr 2709, 1), (Sum.inr 2721, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

theorem sourceEq366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm366 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA366 + difference 2 0) (sourceB366 + difference 0 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA366 + difference 2 0) (sourceB366 + difference 0 2) sourceC366) = raw7201 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7201; decide +kernel
    rw [ha]
    exact (canonical7201 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA366 + difference 2 1) (sourceB366 + difference 1 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA366 + difference 2 1) (sourceB366 + difference 1 2) sourceC366) = raw7209 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7209; decide +kernel
    rw [ha]
    exact (canonical7209 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA366 + difference 2 2) (sourceB366 + difference 2 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA366 + difference 2 2) (sourceB366 + difference 2 2) sourceC366) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA366 + difference 2 3) (sourceB366 + difference 3 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA366 + difference 2 3) (sourceB366 + difference 3 2) sourceC366) = raw7213 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7213; decide +kernel
    rw [ha]
    exact (canonical7213 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA366 + difference 2 4) (sourceB366 + difference 4 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA366 + difference 2 4) (sourceB366 + difference 4 2) sourceC366) = raw7214 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7214; decide +kernel
    rw [ha]
    exact (canonical7214 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA366 + difference 2 5) (sourceB366 + difference 5 2) sourceC366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA366 + difference 2 5) (sourceB366 + difference 5 2) sourceC366) = raw7215 := by
      apply Matrix.ext; unfold tripleCharges sourceA366 sourceB366 sourceC366 difference raw7215; decide +kernel
    rw [ha]
    exact (canonical7215 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA366 + sourceB366) sourceC366) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA366 + sourceB366) sourceC366) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA366 sourceB366 sourceC366 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA366 sourceB366 sourceC366
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm366, Integer.Sparse.eval]
  linarith only [hs]

def sourceA367 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB367 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC367 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm367 : Integer.Sparse Master := [(Sum.inr 2610, 1), (Sum.inr 2612, 1), (Sum.inr 2615, 1), (Sum.inr 2622, 1), (Sum.inr 2709, 1), (Sum.inr 3871, 1), (Sum.inr 4091, -1)]

theorem sourceEq367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm367 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA367 + difference 0 2) (sourceB367 + difference 2 0) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA367 + difference 0 2) (sourceB367 + difference 2 0) sourceC367) = raw7195 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7195; decide +kernel
    rw [ha]
    exact (canonical7195 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA367 + difference 1 2) (sourceB367 + difference 2 1) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2622) := by
    have ha : (tripleCharges (sourceA367 + difference 1 2) (sourceB367 + difference 2 1) sourceC367) = raw7205 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7205; decide +kernel
    rw [ha]
    exact (canonical7205 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA367 + difference 2 2) (sourceB367 + difference 2 2) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA367 + difference 2 2) (sourceB367 + difference 2 2) sourceC367) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA367 + difference 3 2) (sourceB367 + difference 2 3) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA367 + difference 3 2) (sourceB367 + difference 2 3) sourceC367) = raw7216 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7216; decide +kernel
    rw [ha]
    exact (canonical7216 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA367 + difference 4 2) (sourceB367 + difference 2 4) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2612) := by
    have ha : (tripleCharges (sourceA367 + difference 4 2) (sourceB367 + difference 2 4) sourceC367) = raw7217 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7217; decide +kernel
    rw [ha]
    exact (canonical7217 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA367 + difference 5 2) (sourceB367 + difference 2 5) sourceC367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2610) := by
    have ha : (tripleCharges (sourceA367 + difference 5 2) (sourceB367 + difference 2 5) sourceC367) = raw7218 := by
      apply Matrix.ext; unfold tripleCharges sourceA367 sourceB367 sourceC367 difference raw7218; decide +kernel
    rw [ha]
    exact (canonical7218 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA367 + sourceB367) sourceC367) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA367 + sourceB367) sourceC367) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA367 sourceB367 sourceC367 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA367 sourceB367 sourceC367
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm367, Integer.Sparse.eval]
  linarith only [hs]

def sourceA368 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB368 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC368 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm368 : Integer.Sparse Master := [(Sum.inr 1208, 1), (Sum.inr 2473, 1), (Sum.inr 2612, 2), (Sum.inr 2709, 1), (Sum.inr 2710, 1), (Sum.inr 4091, -1)]

theorem sourceEq368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm368 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA368 + difference 4 0) (sourceB368 + difference 0 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1208) := by
    have ha : (tripleCharges (sourceA368 + difference 4 0) (sourceB368 + difference 0 4) sourceC368) = raw7203 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7203; decide +kernel
    rw [ha]
    exact (canonical7203 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA368 + difference 4 1) (sourceB368 + difference 1 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA368 + difference 4 1) (sourceB368 + difference 1 4) sourceC368) = raw7211 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7211; decide +kernel
    rw [ha]
    exact (canonical7211 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA368 + difference 4 2) (sourceB368 + difference 2 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2612) := by
    have ha : (tripleCharges (sourceA368 + difference 4 2) (sourceB368 + difference 2 4) sourceC368) = raw7217 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7217; decide +kernel
    rw [ha]
    exact (canonical7217 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA368 + difference 4 3) (sourceB368 + difference 3 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2612) := by
    have ha : (tripleCharges (sourceA368 + difference 4 3) (sourceB368 + difference 3 4) sourceC368) = raw7219 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7219; decide +kernel
    rw [ha]
    exact (canonical7219 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA368 + difference 4 4) (sourceB368 + difference 4 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA368 + difference 4 4) (sourceB368 + difference 4 4) sourceC368) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA368 + difference 4 5) (sourceB368 + difference 5 4) sourceC368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA368 + difference 4 5) (sourceB368 + difference 5 4) sourceC368) = raw7220 := by
      apply Matrix.ext; unfold tripleCharges sourceA368 sourceB368 sourceC368 difference raw7220; decide +kernel
    rw [ha]
    exact (canonical7220 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA368 + sourceB368) sourceC368) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA368 + sourceB368) sourceC368) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA368 sourceB368 sourceC368 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA368 sourceB368 sourceC368
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm368, Integer.Sparse.eval]
  linarith only [hs]

def sourceA369 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB369 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC369 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm369 : Integer.Sparse Master := [(Sum.inr 4801, 1), (Sum.inr 4803, 2), (Sum.inr 4831, 1), (Sum.inr 4888, 1), (Sum.inr 5219, 1), (Sum.inr 5220, 1), (Sum.inr 5223, 2), (Sum.inr 5241, 1), (Sum.inr 5242, 1), (Sum.inr 5244, 1), (Sum.inr 5249, 1), (Sum.inr 5251, 1), (Sum.inr 5253, 2), (Sum.inr 5254, 2), (Sum.inr 5258, 2), (Sum.inr 5259, 4), (Sum.inr 5266, 2), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5293, 2)]

theorem sourceEq369 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm369 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA369 + difference 0 1) (sourceB369 + difference 1 0) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA369 + difference 0 1) (sourceB369 + difference 1 0) sourceC369) = raw7221 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7221; decide +kernel
    rw [ha]
    exact (canonical7221 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA369 + difference 0 2) (sourceB369 + difference 2 0) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA369 + difference 0 2) (sourceB369 + difference 2 0) sourceC369) = raw6702 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6702; decide +kernel
    rw [ha]
    exact (canonical6702 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA369 + difference 0 3) (sourceB369 + difference 3 0) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA369 + difference 0 3) (sourceB369 + difference 3 0) sourceC369) = raw7222 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7222; decide +kernel
    rw [ha]
    exact (canonical7222 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA369 + difference 0 4) (sourceB369 + difference 4 0) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5242) := by
    have ha : (tripleCharges (sourceA369 + difference 0 4) (sourceB369 + difference 4 0) sourceC369) = raw7223 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7223; decide +kernel
    rw [ha]
    exact (canonical7223 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA369 + difference 0 5) (sourceB369 + difference 5 0) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA369 + difference 0 5) (sourceB369 + difference 5 0) sourceC369) = raw7224 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7224; decide +kernel
    rw [ha]
    exact (canonical7224 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA369 + difference 1 0) (sourceB369 + difference 0 1) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA369 + difference 1 0) (sourceB369 + difference 0 1) sourceC369) = raw5684 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw5684; decide +kernel
    rw [ha]
    exact (canonical5684 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA369 + difference 1 2) (sourceB369 + difference 2 1) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA369 + difference 1 2) (sourceB369 + difference 2 1) sourceC369) = raw6707 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6707; decide +kernel
    rw [ha]
    exact (canonical6707 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA369 + difference 1 3) (sourceB369 + difference 3 1) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA369 + difference 1 3) (sourceB369 + difference 3 1) sourceC369) = raw7225 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7225; decide +kernel
    rw [ha]
    exact (canonical7225 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA369 + difference 1 4) (sourceB369 + difference 4 1) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA369 + difference 1 4) (sourceB369 + difference 4 1) sourceC369) = raw7226 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7226; decide +kernel
    rw [ha]
    exact (canonical7226 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA369 + difference 1 5) (sourceB369 + difference 5 1) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA369 + difference 1 5) (sourceB369 + difference 5 1) sourceC369) = raw5658 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw5658; decide +kernel
    rw [ha]
    exact (canonical5658 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA369 + difference 2 0) (sourceB369 + difference 0 2) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA369 + difference 2 0) (sourceB369 + difference 0 2) sourceC369) = raw7227 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7227; decide +kernel
    rw [ha]
    exact (canonical7227 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA369 + difference 2 1) (sourceB369 + difference 1 2) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5223) := by
    have ha : (tripleCharges (sourceA369 + difference 2 1) (sourceB369 + difference 1 2) sourceC369) = raw7228 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7228; decide +kernel
    rw [ha]
    exact (canonical7228 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA369 + difference 2 3) (sourceB369 + difference 3 2) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA369 + difference 2 3) (sourceB369 + difference 3 2) sourceC369) = raw7229 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7229; decide +kernel
    rw [ha]
    exact (canonical7229 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA369 + difference 2 4) (sourceB369 + difference 4 2) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5253) := by
    have ha : (tripleCharges (sourceA369 + difference 2 4) (sourceB369 + difference 4 2) sourceC369) = raw7230 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7230; decide +kernel
    rw [ha]
    exact (canonical7230 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA369 + difference 2 5) (sourceB369 + difference 5 2) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA369 + difference 2 5) (sourceB369 + difference 5 2) sourceC369) = raw7231 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7231; decide +kernel
    rw [ha]
    exact (canonical7231 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA369 + difference 3 0) (sourceB369 + difference 0 3) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA369 + difference 3 0) (sourceB369 + difference 0 3) sourceC369) = raw6710 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6710; decide +kernel
    rw [ha]
    exact (canonical6710 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA369 + difference 3 1) (sourceB369 + difference 1 3) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5223) := by
    have ha : (tripleCharges (sourceA369 + difference 3 1) (sourceB369 + difference 1 3) sourceC369) = raw6711 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6711; decide +kernel
    rw [ha]
    exact (canonical6711 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA369 + difference 3 2) (sourceB369 + difference 2 3) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA369 + difference 3 2) (sourceB369 + difference 2 3) sourceC369) = raw7063 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7063; decide +kernel
    rw [ha]
    exact (canonical7063 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA369 + difference 3 4) (sourceB369 + difference 4 3) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5253) := by
    have ha : (tripleCharges (sourceA369 + difference 3 4) (sourceB369 + difference 4 3) sourceC369) = raw6713 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6713; decide +kernel
    rw [ha]
    exact (canonical6713 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA369 + difference 3 5) (sourceB369 + difference 5 3) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA369 + difference 3 5) (sourceB369 + difference 5 3) sourceC369) = raw6714 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6714; decide +kernel
    rw [ha]
    exact (canonical6714 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA369 + difference 4 0) (sourceB369 + difference 0 4) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA369 + difference 4 0) (sourceB369 + difference 0 4) sourceC369) = raw7232 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7232; decide +kernel
    rw [ha]
    exact (canonical7232 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA369 + difference 4 1) (sourceB369 + difference 1 4) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA369 + difference 4 1) (sourceB369 + difference 1 4) sourceC369) = raw7233 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7233; decide +kernel
    rw [ha]
    exact (canonical7233 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA369 + difference 4 2) (sourceB369 + difference 2 4) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA369 + difference 4 2) (sourceB369 + difference 2 4) sourceC369) = raw6390 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6390; decide +kernel
    rw [ha]
    exact (canonical6390 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA369 + difference 4 3) (sourceB369 + difference 3 4) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA369 + difference 4 3) (sourceB369 + difference 3 4) sourceC369) = raw7234 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7234; decide +kernel
    rw [ha]
    exact (canonical7234 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA369 + difference 4 5) (sourceB369 + difference 5 4) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA369 + difference 4 5) (sourceB369 + difference 5 4) sourceC369) = raw6379 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6379; decide +kernel
    rw [ha]
    exact (canonical6379 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA369 + difference 5 0) (sourceB369 + difference 0 5) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA369 + difference 5 0) (sourceB369 + difference 0 5) sourceC369) = raw7235 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7235; decide +kernel
    rw [ha]
    exact (canonical7235 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA369 + difference 5 1) (sourceB369 + difference 1 5) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA369 + difference 5 1) (sourceB369 + difference 1 5) sourceC369) = raw7236 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7236; decide +kernel
    rw [ha]
    exact (canonical7236 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA369 + difference 5 2) (sourceB369 + difference 2 5) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA369 + difference 5 2) (sourceB369 + difference 2 5) sourceC369) = raw6726 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw6726; decide +kernel
    rw [ha]
    exact (canonical6726 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA369 + difference 5 3) (sourceB369 + difference 3 5) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA369 + difference 5 3) (sourceB369 + difference 3 5) sourceC369) = raw7237 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7237; decide +kernel
    rw [ha]
    exact (canonical7237 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA369 + difference 5 4) (sourceB369 + difference 4 5) sourceC369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA369 + difference 5 4) (sourceB369 + difference 4 5) sourceC369) = raw7238 := by
      apply Matrix.ext; unfold tripleCharges sourceA369 sourceB369 sourceC369 difference raw7238; decide +kernel
    rw [ha]
    exact (canonical7238 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA369 sourceB369 sourceC369
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm369, Integer.Sparse.eval]
  linarith only [hs]

def sourceA370 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB370 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC370 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm370 : Integer.Sparse Master := [(Sum.inr 2190, 1), (Sum.inr 2191, 1), (Sum.inr 2195, 2), (Sum.inr 2244, 1), (Sum.inr 2661, 1), (Sum.inr 2662, 1), (Sum.inr 2665, 2), (Sum.inr 2708, 1), (Sum.inr 2710, 1), (Sum.inr 2713, 2), (Sum.inr 2714, 2), (Sum.inr 2722, 2), (Sum.inr 2723, 2), (Sum.inr 2731, 2), (Sum.inr 2751, 1), (Sum.inr 2753, 1), (Sum.inr 2767, 2), (Sum.inr 3029, 1), (Sum.inr 3080, 1), (Sum.inr 3081, 1), (Sum.inr 3088, 2)]

theorem sourceEq370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm370 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA370 + difference 0 1) (sourceB370 + difference 1 0) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3029) := by
    have ha : (tripleCharges (sourceA370 + difference 0 1) (sourceB370 + difference 1 0) sourceC370) = raw7239 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7239; decide +kernel
    rw [ha]
    exact (canonical7239 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA370 + difference 0 2) (sourceB370 + difference 2 0) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA370 + difference 0 2) (sourceB370 + difference 2 0) sourceC370) = raw6730 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw6730; decide +kernel
    rw [ha]
    exact (canonical6730 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA370 + difference 0 3) (sourceB370 + difference 3 0) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA370 + difference 0 3) (sourceB370 + difference 3 0) sourceC370) = raw7240 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7240; decide +kernel
    rw [ha]
    exact (canonical7240 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA370 + difference 0 4) (sourceB370 + difference 4 0) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3080) := by
    have ha : (tripleCharges (sourceA370 + difference 0 4) (sourceB370 + difference 4 0) sourceC370) = raw7241 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7241; decide +kernel
    rw [ha]
    exact (canonical7241 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA370 + difference 0 5) (sourceB370 + difference 5 0) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3081) := by
    have ha : (tripleCharges (sourceA370 + difference 0 5) (sourceB370 + difference 5 0) sourceC370) = raw7242 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7242; decide +kernel
    rw [ha]
    exact (canonical7242 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA370 + difference 1 0) (sourceB370 + difference 0 1) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA370 + difference 1 0) (sourceB370 + difference 0 1) sourceC370) = raw5714 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw5714; decide +kernel
    rw [ha]
    exact (canonical5714 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA370 + difference 1 2) (sourceB370 + difference 2 1) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA370 + difference 1 2) (sourceB370 + difference 2 1) sourceC370) = raw6735 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw6735; decide +kernel
    rw [ha]
    exact (canonical6735 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA370 + difference 1 3) (sourceB370 + difference 3 1) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA370 + difference 1 3) (sourceB370 + difference 3 1) sourceC370) = raw7243 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7243; decide +kernel
    rw [ha]
    exact (canonical7243 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA370 + difference 1 4) (sourceB370 + difference 4 1) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA370 + difference 1 4) (sourceB370 + difference 4 1) sourceC370) = raw7244 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7244; decide +kernel
    rw [ha]
    exact (canonical7244 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA370 + difference 1 5) (sourceB370 + difference 5 1) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA370 + difference 1 5) (sourceB370 + difference 5 1) sourceC370) = raw5688 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw5688; decide +kernel
    rw [ha]
    exact (canonical5688 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA370 + difference 2 0) (sourceB370 + difference 0 2) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA370 + difference 2 0) (sourceB370 + difference 0 2) sourceC370) = raw7245 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7245; decide +kernel
    rw [ha]
    exact (canonical7245 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA370 + difference 2 1) (sourceB370 + difference 1 2) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2665) := by
    have ha : (tripleCharges (sourceA370 + difference 2 1) (sourceB370 + difference 1 2) sourceC370) = raw7246 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7246; decide +kernel
    rw [ha]
    exact (canonical7246 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA370 + difference 2 3) (sourceB370 + difference 3 2) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA370 + difference 2 3) (sourceB370 + difference 3 2) sourceC370) = raw7247 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7247; decide +kernel
    rw [ha]
    exact (canonical7247 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA370 + difference 2 4) (sourceB370 + difference 4 2) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2713) := by
    have ha : (tripleCharges (sourceA370 + difference 2 4) (sourceB370 + difference 4 2) sourceC370) = raw7248 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7248; decide +kernel
    rw [ha]
    exact (canonical7248 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA370 + difference 2 5) (sourceB370 + difference 5 2) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA370 + difference 2 5) (sourceB370 + difference 5 2) sourceC370) = raw7249 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7249; decide +kernel
    rw [ha]
    exact (canonical7249 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA370 + difference 3 0) (sourceB370 + difference 0 3) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA370 + difference 3 0) (sourceB370 + difference 0 3) sourceC370) = raw6738 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw6738; decide +kernel
    rw [ha]
    exact (canonical6738 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA370 + difference 3 1) (sourceB370 + difference 1 3) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2665) := by
    have ha : (tripleCharges (sourceA370 + difference 3 1) (sourceB370 + difference 1 3) sourceC370) = raw6739 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw6739; decide +kernel
    rw [ha]
    exact (canonical6739 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA370 + difference 3 2) (sourceB370 + difference 2 3) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA370 + difference 3 2) (sourceB370 + difference 2 3) sourceC370) = raw7077 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7077; decide +kernel
    rw [ha]
    exact (canonical7077 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA370 + difference 3 4) (sourceB370 + difference 4 3) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2713) := by
    have ha : (tripleCharges (sourceA370 + difference 3 4) (sourceB370 + difference 4 3) sourceC370) = raw6741 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw6741; decide +kernel
    rw [ha]
    exact (canonical6741 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA370 + difference 3 5) (sourceB370 + difference 5 3) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA370 + difference 3 5) (sourceB370 + difference 5 3) sourceC370) = raw6742 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw6742; decide +kernel
    rw [ha]
    exact (canonical6742 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA370 + difference 4 0) (sourceB370 + difference 0 4) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA370 + difference 4 0) (sourceB370 + difference 0 4) sourceC370) = raw7250 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7250; decide +kernel
    rw [ha]
    exact (canonical7250 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA370 + difference 4 1) (sourceB370 + difference 1 4) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA370 + difference 4 1) (sourceB370 + difference 1 4) sourceC370) = raw7251 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7251; decide +kernel
    rw [ha]
    exact (canonical7251 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA370 + difference 4 2) (sourceB370 + difference 2 4) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA370 + difference 4 2) (sourceB370 + difference 2 4) sourceC370) = raw6412 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw6412; decide +kernel
    rw [ha]
    exact (canonical6412 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA370 + difference 4 3) (sourceB370 + difference 3 4) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA370 + difference 4 3) (sourceB370 + difference 3 4) sourceC370) = raw7252 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7252; decide +kernel
    rw [ha]
    exact (canonical7252 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA370 + difference 4 5) (sourceB370 + difference 5 4) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA370 + difference 4 5) (sourceB370 + difference 5 4) sourceC370) = raw6401 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw6401; decide +kernel
    rw [ha]
    exact (canonical6401 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA370 + difference 5 0) (sourceB370 + difference 0 5) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA370 + difference 5 0) (sourceB370 + difference 0 5) sourceC370) = raw7253 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7253; decide +kernel
    rw [ha]
    exact (canonical7253 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA370 + difference 5 1) (sourceB370 + difference 1 5) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA370 + difference 5 1) (sourceB370 + difference 1 5) sourceC370) = raw7254 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7254; decide +kernel
    rw [ha]
    exact (canonical7254 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA370 + difference 5 2) (sourceB370 + difference 2 5) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA370 + difference 5 2) (sourceB370 + difference 2 5) sourceC370) = raw6754 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw6754; decide +kernel
    rw [ha]
    exact (canonical6754 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA370 + difference 5 3) (sourceB370 + difference 3 5) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA370 + difference 5 3) (sourceB370 + difference 3 5) sourceC370) = raw7255 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7255; decide +kernel
    rw [ha]
    exact (canonical7255 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA370 + difference 5 4) (sourceB370 + difference 4 5) sourceC370) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA370 + difference 5 4) (sourceB370 + difference 4 5) sourceC370) = raw7256 := by
      apply Matrix.ext; unfold tripleCharges sourceA370 sourceB370 sourceC370 difference raw7256; decide +kernel
    rw [ha]
    exact (canonical7256 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA370 sourceB370 sourceC370
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm370, Integer.Sparse.eval]
  linarith only [hs]

def sourceA371 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB371 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC371 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm371 : Integer.Sparse Master := [(Sum.inr 2694, 1), (Sum.inr 2695, 1), (Sum.inr 2698, 1), (Sum.inr 2723, 2), (Sum.inr 3016, 2), (Sum.inr 3017, 2), (Sum.inr 3019, 2), (Sum.inr 3039, 2), (Sum.inr 3064, 1), (Sum.inr 3066, 1), (Sum.inr 3068, 1), (Sum.inr 3069, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1), (Sum.inr 3088, 2), (Sum.inr 3089, 2), (Sum.inr 3102, 2), (Sum.inr 3202, 2), (Sum.inr 3205, 1), (Sum.inr 3209, 1), (Sum.inr 3227, 1)]

theorem sourceEq371 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm371 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA371 + difference 0 1) (sourceB371 + difference 1 0) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA371 + difference 0 1) (sourceB371 + difference 1 0) sourceC371) = raw7257 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7257; decide +kernel
    rw [ha]
    exact (canonical7257 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA371 + difference 0 2) (sourceB371 + difference 2 0) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA371 + difference 0 2) (sourceB371 + difference 2 0) sourceC371) = raw6758 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw6758; decide +kernel
    rw [ha]
    exact (canonical6758 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA371 + difference 0 3) (sourceB371 + difference 3 0) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA371 + difference 0 3) (sourceB371 + difference 3 0) sourceC371) = raw7258 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7258; decide +kernel
    rw [ha]
    exact (canonical7258 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA371 + difference 0 4) (sourceB371 + difference 4 0) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA371 + difference 0 4) (sourceB371 + difference 4 0) sourceC371) = raw7259 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7259; decide +kernel
    rw [ha]
    exact (canonical7259 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA371 + difference 0 5) (sourceB371 + difference 5 0) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA371 + difference 0 5) (sourceB371 + difference 5 0) sourceC371) = raw7260 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7260; decide +kernel
    rw [ha]
    exact (canonical7260 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA371 + difference 1 0) (sourceB371 + difference 0 1) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA371 + difference 1 0) (sourceB371 + difference 0 1) sourceC371) = raw5744 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw5744; decide +kernel
    rw [ha]
    exact (canonical5744 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA371 + difference 1 2) (sourceB371 + difference 2 1) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA371 + difference 1 2) (sourceB371 + difference 2 1) sourceC371) = raw6763 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw6763; decide +kernel
    rw [ha]
    exact (canonical6763 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA371 + difference 1 3) (sourceB371 + difference 3 1) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA371 + difference 1 3) (sourceB371 + difference 3 1) sourceC371) = raw7261 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7261; decide +kernel
    rw [ha]
    exact (canonical7261 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA371 + difference 1 4) (sourceB371 + difference 4 1) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA371 + difference 1 4) (sourceB371 + difference 4 1) sourceC371) = raw7262 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7262; decide +kernel
    rw [ha]
    exact (canonical7262 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA371 + difference 1 5) (sourceB371 + difference 5 1) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA371 + difference 1 5) (sourceB371 + difference 5 1) sourceC371) = raw5718 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw5718; decide +kernel
    rw [ha]
    exact (canonical5718 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA371 + difference 2 0) (sourceB371 + difference 0 2) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA371 + difference 2 0) (sourceB371 + difference 0 2) sourceC371) = raw7263 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7263; decide +kernel
    rw [ha]
    exact (canonical7263 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA371 + difference 2 1) (sourceB371 + difference 1 2) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3019) := by
    have ha : (tripleCharges (sourceA371 + difference 2 1) (sourceB371 + difference 1 2) sourceC371) = raw7264 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7264; decide +kernel
    rw [ha]
    exact (canonical7264 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA371 + difference 2 3) (sourceB371 + difference 3 2) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA371 + difference 2 3) (sourceB371 + difference 3 2) sourceC371) = raw7265 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7265; decide +kernel
    rw [ha]
    exact (canonical7265 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA371 + difference 2 4) (sourceB371 + difference 4 2) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3017) := by
    have ha : (tripleCharges (sourceA371 + difference 2 4) (sourceB371 + difference 4 2) sourceC371) = raw7266 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7266; decide +kernel
    rw [ha]
    exact (canonical7266 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA371 + difference 2 5) (sourceB371 + difference 5 2) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA371 + difference 2 5) (sourceB371 + difference 5 2) sourceC371) = raw7267 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7267; decide +kernel
    rw [ha]
    exact (canonical7267 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA371 + difference 3 0) (sourceB371 + difference 0 3) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA371 + difference 3 0) (sourceB371 + difference 0 3) sourceC371) = raw6766 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw6766; decide +kernel
    rw [ha]
    exact (canonical6766 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA371 + difference 3 1) (sourceB371 + difference 1 3) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3019) := by
    have ha : (tripleCharges (sourceA371 + difference 3 1) (sourceB371 + difference 1 3) sourceC371) = raw6767 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw6767; decide +kernel
    rw [ha]
    exact (canonical6767 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA371 + difference 3 2) (sourceB371 + difference 2 3) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA371 + difference 3 2) (sourceB371 + difference 2 3) sourceC371) = raw7091 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7091; decide +kernel
    rw [ha]
    exact (canonical7091 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA371 + difference 3 4) (sourceB371 + difference 4 3) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3017) := by
    have ha : (tripleCharges (sourceA371 + difference 3 4) (sourceB371 + difference 4 3) sourceC371) = raw6769 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw6769; decide +kernel
    rw [ha]
    exact (canonical6769 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA371 + difference 3 5) (sourceB371 + difference 5 3) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA371 + difference 3 5) (sourceB371 + difference 5 3) sourceC371) = raw6770 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw6770; decide +kernel
    rw [ha]
    exact (canonical6770 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA371 + difference 4 0) (sourceB371 + difference 0 4) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3209) := by
    have ha : (tripleCharges (sourceA371 + difference 4 0) (sourceB371 + difference 0 4) sourceC371) = raw7268 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7268; decide +kernel
    rw [ha]
    exact (canonical7268 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA371 + difference 4 1) (sourceB371 + difference 1 4) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA371 + difference 4 1) (sourceB371 + difference 1 4) sourceC371) = raw7269 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7269; decide +kernel
    rw [ha]
    exact (canonical7269 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA371 + difference 4 2) (sourceB371 + difference 2 4) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA371 + difference 4 2) (sourceB371 + difference 2 4) sourceC371) = raw6434 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw6434; decide +kernel
    rw [ha]
    exact (canonical6434 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA371 + difference 4 3) (sourceB371 + difference 3 4) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA371 + difference 4 3) (sourceB371 + difference 3 4) sourceC371) = raw7270 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7270; decide +kernel
    rw [ha]
    exact (canonical7270 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA371 + difference 4 5) (sourceB371 + difference 5 4) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA371 + difference 4 5) (sourceB371 + difference 5 4) sourceC371) = raw6423 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw6423; decide +kernel
    rw [ha]
    exact (canonical6423 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA371 + difference 5 0) (sourceB371 + difference 0 5) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3205) := by
    have ha : (tripleCharges (sourceA371 + difference 5 0) (sourceB371 + difference 0 5) sourceC371) = raw7271 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7271; decide +kernel
    rw [ha]
    exact (canonical7271 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA371 + difference 5 1) (sourceB371 + difference 1 5) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3069) := by
    have ha : (tripleCharges (sourceA371 + difference 5 1) (sourceB371 + difference 1 5) sourceC371) = raw7272 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7272; decide +kernel
    rw [ha]
    exact (canonical7272 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA371 + difference 5 2) (sourceB371 + difference 2 5) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA371 + difference 5 2) (sourceB371 + difference 2 5) sourceC371) = raw6782 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw6782; decide +kernel
    rw [ha]
    exact (canonical6782 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA371 + difference 5 3) (sourceB371 + difference 3 5) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA371 + difference 5 3) (sourceB371 + difference 3 5) sourceC371) = raw7273 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7273; decide +kernel
    rw [ha]
    exact (canonical7273 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA371 + difference 5 4) (sourceB371 + difference 4 5) sourceC371) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA371 + difference 5 4) (sourceB371 + difference 4 5) sourceC371) = raw7274 := by
      apply Matrix.ext; unfold tripleCharges sourceA371 sourceB371 sourceC371 difference raw7274; decide +kernel
    rw [ha]
    exact (canonical7274 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA371 sourceB371 sourceC371
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm371, Integer.Sparse.eval]
  linarith only [hs]

def sourceA372 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB372 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC372 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm372 : Integer.Sparse Master := [(Sum.inr 3493, 1), (Sum.inr 3494, 1), (Sum.inr 3497, 1), (Sum.inr 3531, 1), (Sum.inr 3544, 2), (Sum.inr 4084, -1)]

theorem sourceEq372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm372 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA372 + difference 0 0) (sourceB372 + difference 0 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA372 + difference 0 0) (sourceB372 + difference 0 0) sourceC372) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA372 + difference 0 1) (sourceB372 + difference 1 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA372 + difference 0 1) (sourceB372 + difference 1 0) sourceC372) = raw7275 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw7275; decide +kernel
    rw [ha]
    exact (canonical7275 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA372 + difference 0 2) (sourceB372 + difference 2 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA372 + difference 0 2) (sourceB372 + difference 2 0) sourceC372) = raw6787 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw6787; decide +kernel
    rw [ha]
    exact (canonical6787 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA372 + difference 0 3) (sourceB372 + difference 3 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA372 + difference 0 3) (sourceB372 + difference 3 0) sourceC372) = raw7276 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw7276; decide +kernel
    rw [ha]
    exact (canonical7276 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA372 + difference 0 4) (sourceB372 + difference 4 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3494) := by
    have ha : (tripleCharges (sourceA372 + difference 0 4) (sourceB372 + difference 4 0) sourceC372) = raw7277 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw7277; decide +kernel
    rw [ha]
    exact (canonical7277 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA372 + difference 0 5) (sourceB372 + difference 5 0) sourceC372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3493) := by
    have ha : (tripleCharges (sourceA372 + difference 0 5) (sourceB372 + difference 5 0) sourceC372) = raw7278 := by
      apply Matrix.ext; unfold tripleCharges sourceA372 sourceB372 sourceC372 difference raw7278; decide +kernel
    rw [ha]
    exact (canonical7278 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA372 + sourceB372) sourceC372) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA372 + sourceB372) sourceC372) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA372 sourceB372 sourceC372 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA372 sourceB372 sourceC372
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm372, Integer.Sparse.eval]
  linarith only [hs]

def sourceA373 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB373 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC373 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm373 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 2021, 2), (Sum.inr 2051, 1), (Sum.inr 2262, 1), (Sum.inr 3531, 1), (Sum.inr 4084, -1)]

theorem sourceEq373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm373 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA373 + difference 0 0) (sourceB373 + difference 0 0) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA373 + difference 0 0) (sourceB373 + difference 0 0) sourceC373) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA373 + difference 1 0) (sourceB373 + difference 0 1) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA373 + difference 1 0) (sourceB373 + difference 0 1) sourceC373) = raw5768 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw5768; decide +kernel
    rw [ha]
    exact (canonical5768 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA373 + difference 2 0) (sourceB373 + difference 0 2) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA373 + difference 2 0) (sourceB373 + difference 0 2) sourceC373) = raw7279 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw7279; decide +kernel
    rw [ha]
    exact (canonical7279 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA373 + difference 3 0) (sourceB373 + difference 0 3) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA373 + difference 3 0) (sourceB373 + difference 0 3) sourceC373) = raw6791 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw6791; decide +kernel
    rw [ha]
    exact (canonical6791 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA373 + difference 4 0) (sourceB373 + difference 0 4) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA373 + difference 4 0) (sourceB373 + difference 0 4) sourceC373) = raw7280 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw7280; decide +kernel
    rw [ha]
    exact (canonical7280 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA373 + difference 5 0) (sourceB373 + difference 0 5) sourceC373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2019) := by
    have ha : (tripleCharges (sourceA373 + difference 5 0) (sourceB373 + difference 0 5) sourceC373) = raw7281 := by
      apply Matrix.ext; unfold tripleCharges sourceA373 sourceB373 sourceC373 difference raw7281; decide +kernel
    rw [ha]
    exact (canonical7281 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA373 + sourceB373) sourceC373) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA373 + sourceB373) sourceC373) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA373 sourceB373 sourceC373 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA373 sourceB373 sourceC373
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm373, Integer.Sparse.eval]
  linarith only [hs]

def sourceA374 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB374 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC374 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm374 : Integer.Sparse Master := [(Sum.inr 2262, 1), (Sum.inr 3531, 1), (Sum.inr 3580, 1), (Sum.inr 3625, 1), (Sum.inr 3627, 2), (Sum.inr 4084, -1)]

theorem sourceEq374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm374 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA374 + difference 1 0) (sourceB374 + difference 0 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA374 + difference 1 0) (sourceB374 + difference 0 1) sourceC374) = raw5768 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw5768; decide +kernel
    rw [ha]
    exact (canonical5768 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA374 + difference 1 1) (sourceB374 + difference 1 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA374 + difference 1 1) (sourceB374 + difference 1 1) sourceC374) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA374 + difference 1 2) (sourceB374 + difference 2 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA374 + difference 1 2) (sourceB374 + difference 2 1) sourceC374) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA374 + difference 1 3) (sourceB374 + difference 3 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA374 + difference 1 3) (sourceB374 + difference 3 1) sourceC374) = raw7282 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw7282; decide +kernel
    rw [ha]
    exact (canonical7282 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA374 + difference 1 4) (sourceB374 + difference 4 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA374 + difference 1 4) (sourceB374 + difference 4 1) sourceC374) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA374 + difference 1 5) (sourceB374 + difference 5 1) sourceC374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA374 + difference 1 5) (sourceB374 + difference 5 1) sourceC374) = raw5749 := by
      apply Matrix.ext; unfold tripleCharges sourceA374 sourceB374 sourceC374 difference raw5749; decide +kernel
    rw [ha]
    exact (canonical5749 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA374 + sourceB374) sourceC374) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA374 + sourceB374) sourceC374) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA374 sourceB374 sourceC374 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA374 sourceB374 sourceC374
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm374, Integer.Sparse.eval]
  linarith only [hs]

def sourceA375 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB375 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC375 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm375 : Integer.Sparse Master := [(Sum.inr 3375, 1), (Sum.inr 3377, 2), (Sum.inr 3388, 1), (Sum.inr 3497, 1), (Sum.inr 3531, 1), (Sum.inr 4084, -1)]

theorem sourceEq375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm375 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA375 + difference 0 1) (sourceB375 + difference 1 0) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA375 + difference 0 1) (sourceB375 + difference 1 0) sourceC375) = raw7275 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw7275; decide +kernel
    rw [ha]
    exact (canonical7275 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA375 + difference 1 1) (sourceB375 + difference 1 1) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA375 + difference 1 1) (sourceB375 + difference 1 1) sourceC375) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA375 + difference 2 1) (sourceB375 + difference 1 2) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3377) := by
    have ha : (tripleCharges (sourceA375 + difference 2 1) (sourceB375 + difference 1 2) sourceC375) = raw7284 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw7284; decide +kernel
    rw [ha]
    exact (canonical7284 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA375 + difference 3 1) (sourceB375 + difference 1 3) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3377) := by
    have ha : (tripleCharges (sourceA375 + difference 3 1) (sourceB375 + difference 1 3) sourceC375) = raw6799 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw6799; decide +kernel
    rw [ha]
    exact (canonical6799 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA375 + difference 4 1) (sourceB375 + difference 1 4) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA375 + difference 4 1) (sourceB375 + difference 1 4) sourceC375) = raw7285 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw7285; decide +kernel
    rw [ha]
    exact (canonical7285 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA375 + difference 5 1) (sourceB375 + difference 1 5) sourceC375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3375) := by
    have ha : (tripleCharges (sourceA375 + difference 5 1) (sourceB375 + difference 1 5) sourceC375) = raw7286 := by
      apply Matrix.ext; unfold tripleCharges sourceA375 sourceB375 sourceC375 difference raw7286; decide +kernel
    rw [ha]
    exact (canonical7286 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA375 + sourceB375) sourceC375) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA375 + sourceB375) sourceC375) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA375 sourceB375 sourceC375 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA375 sourceB375 sourceC375
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm375, Integer.Sparse.eval]
  linarith only [hs]

def sourceA376 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB376 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC376 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm376 : Integer.Sparse Master := [(Sum.inr 2051, 1), (Sum.inr 3388, 1), (Sum.inr 3531, 1), (Sum.inr 3539, 1), (Sum.inr 3544, 2), (Sum.inr 4084, -1)]

theorem sourceEq376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm376 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA376 + difference 4 0) (sourceB376 + difference 0 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA376 + difference 4 0) (sourceB376 + difference 0 4) sourceC376) = raw7280 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw7280; decide +kernel
    rw [ha]
    exact (canonical7280 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA376 + difference 4 1) (sourceB376 + difference 1 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA376 + difference 4 1) (sourceB376 + difference 1 4) sourceC376) = raw7285 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw7285; decide +kernel
    rw [ha]
    exact (canonical7285 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA376 + difference 4 2) (sourceB376 + difference 2 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA376 + difference 4 2) (sourceB376 + difference 2 4) sourceC376) = raw6456 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw6456; decide +kernel
    rw [ha]
    exact (canonical6456 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA376 + difference 4 3) (sourceB376 + difference 3 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA376 + difference 4 3) (sourceB376 + difference 3 4) sourceC376) = raw7287 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw7287; decide +kernel
    rw [ha]
    exact (canonical7287 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA376 + difference 4 4) (sourceB376 + difference 4 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA376 + difference 4 4) (sourceB376 + difference 4 4) sourceC376) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA376 + difference 4 5) (sourceB376 + difference 5 4) sourceC376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA376 + difference 4 5) (sourceB376 + difference 5 4) sourceC376) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA376 sourceB376 sourceC376 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA376 + sourceB376) sourceC376) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA376 + sourceB376) sourceC376) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA376 sourceB376 sourceC376 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA376 sourceB376 sourceC376
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm376, Integer.Sparse.eval]
  linarith only [hs]

def sourceA377 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB377 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC377 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm377 : Integer.Sparse Master := [(Sum.inr 3494, 1), (Sum.inr 3502, 1), (Sum.inr 3504, 2), (Sum.inr 3531, 1), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

theorem sourceEq377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm377 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA377 + difference 0 4) (sourceB377 + difference 4 0) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3494) := by
    have ha : (tripleCharges (sourceA377 + difference 0 4) (sourceB377 + difference 4 0) sourceC377) = raw7277 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw7277; decide +kernel
    rw [ha]
    exact (canonical7277 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA377 + difference 1 4) (sourceB377 + difference 4 1) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA377 + difference 1 4) (sourceB377 + difference 4 1) sourceC377) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA377 + difference 2 4) (sourceB377 + difference 4 2) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3504) := by
    have ha : (tripleCharges (sourceA377 + difference 2 4) (sourceB377 + difference 4 2) sourceC377) = raw7288 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw7288; decide +kernel
    rw [ha]
    exact (canonical7288 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA377 + difference 3 4) (sourceB377 + difference 4 3) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3504) := by
    have ha : (tripleCharges (sourceA377 + difference 3 4) (sourceB377 + difference 4 3) sourceC377) = raw6804 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw6804; decide +kernel
    rw [ha]
    exact (canonical6804 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA377 + difference 4 4) (sourceB377 + difference 4 4) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA377 + difference 4 4) (sourceB377 + difference 4 4) sourceC377) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA377 + difference 5 4) (sourceB377 + difference 4 5) sourceC377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA377 + difference 5 4) (sourceB377 + difference 4 5) sourceC377) = raw7289 := by
      apply Matrix.ext; unfold tripleCharges sourceA377 sourceB377 sourceC377 difference raw7289; decide +kernel
    rw [ha]
    exact (canonical7289 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA377 + sourceB377) sourceC377) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA377 + sourceB377) sourceC377) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA377 sourceB377 sourceC377 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA377 sourceB377 sourceC377
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm377, Integer.Sparse.eval]
  linarith only [hs]

def sourceA378 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB378 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC378 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm378 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 3375, 1), (Sum.inr 3502, 1), (Sum.inr 3531, 1), (Sum.inr 3533, 2), (Sum.inr 4084, -1)]

theorem sourceEq378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm378 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA378 + difference 5 0) (sourceB378 + difference 0 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2019) := by
    have ha : (tripleCharges (sourceA378 + difference 5 0) (sourceB378 + difference 0 5) sourceC378) = raw7281 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw7281; decide +kernel
    rw [ha]
    exact (canonical7281 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA378 + difference 5 1) (sourceB378 + difference 1 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3375) := by
    have ha : (tripleCharges (sourceA378 + difference 5 1) (sourceB378 + difference 1 5) sourceC378) = raw7286 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw7286; decide +kernel
    rw [ha]
    exact (canonical7286 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA378 + difference 5 2) (sourceB378 + difference 2 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA378 + difference 5 2) (sourceB378 + difference 2 5) sourceC378) = raw6811 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw6811; decide +kernel
    rw [ha]
    exact (canonical6811 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA378 + difference 5 3) (sourceB378 + difference 3 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA378 + difference 5 3) (sourceB378 + difference 3 5) sourceC378) = raw7290 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw7290; decide +kernel
    rw [ha]
    exact (canonical7290 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA378 + difference 5 4) (sourceB378 + difference 4 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA378 + difference 5 4) (sourceB378 + difference 4 5) sourceC378) = raw7289 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw7289; decide +kernel
    rw [ha]
    exact (canonical7289 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA378 + difference 5 5) (sourceB378 + difference 5 5) sourceC378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA378 + difference 5 5) (sourceB378 + difference 5 5) sourceC378) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA378 sourceB378 sourceC378 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA378 + sourceB378) sourceC378) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA378 + sourceB378) sourceC378) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA378 sourceB378 sourceC378 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA378 sourceB378 sourceC378
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm378, Integer.Sparse.eval]
  linarith only [hs]

def sourceA379 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB379 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC379 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm379 : Integer.Sparse Master := [(Sum.inr 4576, 1), (Sum.inr 4578, 1), (Sum.inr 4580, 1), (Sum.inr 4589, 2), (Sum.inr 4780, 2), (Sum.inr 4792, 1), (Sum.inr 4830, 1), (Sum.inr 5067, 1), (Sum.inr 5076, 2), (Sum.inr 5182, 2), (Sum.inr 5187, 2), (Sum.inr 5191, 2), (Sum.inr 5250, 1), (Sum.inr 5251, 2), (Sum.inr 5257, 2), (Sum.inr 5277, 1), (Sum.inr 5281, 1), (Sum.inr 5406, 1), (Sum.inr 5425, 2), (Sum.inr 5433, 1), (Sum.inr 5437, 1)]

theorem sourceEq379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm379 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA379 + difference 0 1) (sourceB379 + difference 1 0) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA379 + difference 0 1) (sourceB379 + difference 1 0) sourceC379) = raw7291 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7291; decide +kernel
    rw [ha]
    exact (canonical7291 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA379 + difference 0 2) (sourceB379 + difference 2 0) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA379 + difference 0 2) (sourceB379 + difference 2 0) sourceC379) = raw7292 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7292; decide +kernel
    rw [ha]
    exact (canonical7292 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA379 + difference 0 3) (sourceB379 + difference 3 0) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA379 + difference 0 3) (sourceB379 + difference 3 0) sourceC379) = raw7293 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7293; decide +kernel
    rw [ha]
    exact (canonical7293 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA379 + difference 0 4) (sourceB379 + difference 4 0) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA379 + difference 0 4) (sourceB379 + difference 4 0) sourceC379) = raw7294 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7294; decide +kernel
    rw [ha]
    exact (canonical7294 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA379 + difference 0 5) (sourceB379 + difference 5 0) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA379 + difference 0 5) (sourceB379 + difference 5 0) sourceC379) = raw7295 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7295; decide +kernel
    rw [ha]
    exact (canonical7295 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA379 + difference 1 0) (sourceB379 + difference 0 1) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4580) := by
    have ha : (tripleCharges (sourceA379 + difference 1 0) (sourceB379 + difference 0 1) sourceC379) = raw7296 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7296; decide +kernel
    rw [ha]
    exact (canonical7296 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA379 + difference 1 2) (sourceB379 + difference 2 1) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5191) := by
    have ha : (tripleCharges (sourceA379 + difference 1 2) (sourceB379 + difference 2 1) sourceC379) = raw7297 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7297; decide +kernel
    rw [ha]
    exact (canonical7297 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA379 + difference 1 3) (sourceB379 + difference 3 1) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5191) := by
    have ha : (tripleCharges (sourceA379 + difference 1 3) (sourceB379 + difference 3 1) sourceC379) = raw7298 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7298; decide +kernel
    rw [ha]
    exact (canonical7298 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA379 + difference 1 4) (sourceB379 + difference 4 1) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5277) := by
    have ha : (tripleCharges (sourceA379 + difference 1 4) (sourceB379 + difference 4 1) sourceC379) = raw7299 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7299; decide +kernel
    rw [ha]
    exact (canonical7299 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA379 + difference 1 5) (sourceB379 + difference 5 1) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA379 + difference 1 5) (sourceB379 + difference 5 1) sourceC379) = raw7300 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7300; decide +kernel
    rw [ha]
    exact (canonical7300 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA379 + difference 2 0) (sourceB379 + difference 0 2) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA379 + difference 2 0) (sourceB379 + difference 0 2) sourceC379) = raw7301 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7301; decide +kernel
    rw [ha]
    exact (canonical7301 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA379 + difference 2 1) (sourceB379 + difference 1 2) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA379 + difference 2 1) (sourceB379 + difference 1 2) sourceC379) = raw7302 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7302; decide +kernel
    rw [ha]
    exact (canonical7302 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA379 + difference 2 3) (sourceB379 + difference 3 2) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA379 + difference 2 3) (sourceB379 + difference 3 2) sourceC379) = raw7303 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7303; decide +kernel
    rw [ha]
    exact (canonical7303 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA379 + difference 2 4) (sourceB379 + difference 4 2) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA379 + difference 2 4) (sourceB379 + difference 4 2) sourceC379) = raw7304 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7304; decide +kernel
    rw [ha]
    exact (canonical7304 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA379 + difference 2 5) (sourceB379 + difference 5 2) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA379 + difference 2 5) (sourceB379 + difference 5 2) sourceC379) = raw7305 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7305; decide +kernel
    rw [ha]
    exact (canonical7305 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA379 + difference 3 0) (sourceB379 + difference 0 3) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA379 + difference 3 0) (sourceB379 + difference 0 3) sourceC379) = raw7306 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7306; decide +kernel
    rw [ha]
    exact (canonical7306 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA379 + difference 3 1) (sourceB379 + difference 1 3) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA379 + difference 3 1) (sourceB379 + difference 1 3) sourceC379) = raw7307 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7307; decide +kernel
    rw [ha]
    exact (canonical7307 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA379 + difference 3 2) (sourceB379 + difference 2 3) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA379 + difference 3 2) (sourceB379 + difference 2 3) sourceC379) = raw7308 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7308; decide +kernel
    rw [ha]
    exact (canonical7308 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA379 + difference 3 4) (sourceB379 + difference 4 3) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA379 + difference 3 4) (sourceB379 + difference 4 3) sourceC379) = raw7309 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7309; decide +kernel
    rw [ha]
    exact (canonical7309 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA379 + difference 3 5) (sourceB379 + difference 5 3) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA379 + difference 3 5) (sourceB379 + difference 5 3) sourceC379) = raw7310 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7310; decide +kernel
    rw [ha]
    exact (canonical7310 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA379 + difference 4 0) (sourceB379 + difference 0 4) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4578) := by
    have ha : (tripleCharges (sourceA379 + difference 4 0) (sourceB379 + difference 0 4) sourceC379) = raw7311 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7311; decide +kernel
    rw [ha]
    exact (canonical7311 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA379 + difference 4 1) (sourceB379 + difference 1 4) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA379 + difference 4 1) (sourceB379 + difference 1 4) sourceC379) = raw7312 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7312; decide +kernel
    rw [ha]
    exact (canonical7312 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA379 + difference 4 2) (sourceB379 + difference 2 4) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5182) := by
    have ha : (tripleCharges (sourceA379 + difference 4 2) (sourceB379 + difference 2 4) sourceC379) = raw7313 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7313; decide +kernel
    rw [ha]
    exact (canonical7313 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA379 + difference 4 3) (sourceB379 + difference 3 4) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5182) := by
    have ha : (tripleCharges (sourceA379 + difference 4 3) (sourceB379 + difference 3 4) sourceC379) = raw7314 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7314; decide +kernel
    rw [ha]
    exact (canonical7314 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA379 + difference 4 5) (sourceB379 + difference 5 4) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA379 + difference 4 5) (sourceB379 + difference 5 4) sourceC379) = raw7315 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7315; decide +kernel
    rw [ha]
    exact (canonical7315 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA379 + difference 5 0) (sourceB379 + difference 0 5) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4576) := by
    have ha : (tripleCharges (sourceA379 + difference 5 0) (sourceB379 + difference 0 5) sourceC379) = raw7316 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7316; decide +kernel
    rw [ha]
    exact (canonical7316 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA379 + difference 5 1) (sourceB379 + difference 1 5) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA379 + difference 5 1) (sourceB379 + difference 1 5) sourceC379) = raw7317 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7317; decide +kernel
    rw [ha]
    exact (canonical7317 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA379 + difference 5 2) (sourceB379 + difference 2 5) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4780) := by
    have ha : (tripleCharges (sourceA379 + difference 5 2) (sourceB379 + difference 2 5) sourceC379) = raw7318 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7318; decide +kernel
    rw [ha]
    exact (canonical7318 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA379 + difference 5 3) (sourceB379 + difference 3 5) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4780) := by
    have ha : (tripleCharges (sourceA379 + difference 5 3) (sourceB379 + difference 3 5) sourceC379) = raw7319 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7319; decide +kernel
    rw [ha]
    exact (canonical7319 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA379 + difference 5 4) (sourceB379 + difference 4 5) sourceC379) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4830) := by
    have ha : (tripleCharges (sourceA379 + difference 5 4) (sourceB379 + difference 4 5) sourceC379) = raw7320 := by
      apply Matrix.ext; unfold tripleCharges sourceA379 sourceB379 sourceC379 difference raw7320; decide +kernel
    rw [ha]
    exact (canonical7320 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA379 sourceB379 sourceC379
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm379, Integer.Sparse.eval]
  linarith only [hs]

def sourceA380 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB380 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC380 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm380 : Integer.Sparse Master := [(Sum.inr 1194, 1), (Sum.inr 1196, 1), (Sum.inr 1198, 1), (Sum.inr 1212, 2), (Sum.inr 1988, 2), (Sum.inr 2009, 1), (Sum.inr 2187, 1), (Sum.inr 2850, 2), (Sum.inr 2852, 2), (Sum.inr 2861, 2), (Sum.inr 2981, 1), (Sum.inr 2986, 2), (Sum.inr 3059, 1), (Sum.inr 3064, 2), (Sum.inr 3065, 1), (Sum.inr 3074, 1), (Sum.inr 3087, 2), (Sum.inr 3839, 2), (Sum.inr 3847, 1), (Sum.inr 3899, 1), (Sum.inr 4033, 1)]

theorem sourceEq380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm380 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA380 + difference 0 1) (sourceB380 + difference 1 0) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA380 + difference 0 1) (sourceB380 + difference 1 0) sourceC380) = raw7321 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7321; decide +kernel
    rw [ha]
    exact (canonical7321 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA380 + difference 0 2) (sourceB380 + difference 2 0) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA380 + difference 0 2) (sourceB380 + difference 2 0) sourceC380) = raw7322 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7322; decide +kernel
    rw [ha]
    exact (canonical7322 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA380 + difference 0 3) (sourceB380 + difference 3 0) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA380 + difference 0 3) (sourceB380 + difference 3 0) sourceC380) = raw7323 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7323; decide +kernel
    rw [ha]
    exact (canonical7323 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA380 + difference 0 4) (sourceB380 + difference 4 0) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA380 + difference 0 4) (sourceB380 + difference 4 0) sourceC380) = raw7324 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7324; decide +kernel
    rw [ha]
    exact (canonical7324 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA380 + difference 0 5) (sourceB380 + difference 5 0) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA380 + difference 0 5) (sourceB380 + difference 5 0) sourceC380) = raw7325 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7325; decide +kernel
    rw [ha]
    exact (canonical7325 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA380 + difference 1 0) (sourceB380 + difference 0 1) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1198) := by
    have ha : (tripleCharges (sourceA380 + difference 1 0) (sourceB380 + difference 0 1) sourceC380) = raw7326 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7326; decide +kernel
    rw [ha]
    exact (canonical7326 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA380 + difference 1 2) (sourceB380 + difference 2 1) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2852) := by
    have ha : (tripleCharges (sourceA380 + difference 1 2) (sourceB380 + difference 2 1) sourceC380) = raw7327 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7327; decide +kernel
    rw [ha]
    exact (canonical7327 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA380 + difference 1 3) (sourceB380 + difference 3 1) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2852) := by
    have ha : (tripleCharges (sourceA380 + difference 1 3) (sourceB380 + difference 3 1) sourceC380) = raw7328 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7328; decide +kernel
    rw [ha]
    exact (canonical7328 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA380 + difference 1 4) (sourceB380 + difference 4 1) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA380 + difference 1 4) (sourceB380 + difference 4 1) sourceC380) = raw7329 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7329; decide +kernel
    rw [ha]
    exact (canonical7329 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA380 + difference 1 5) (sourceB380 + difference 5 1) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA380 + difference 1 5) (sourceB380 + difference 5 1) sourceC380) = raw7330 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7330; decide +kernel
    rw [ha]
    exact (canonical7330 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA380 + difference 2 0) (sourceB380 + difference 0 2) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA380 + difference 2 0) (sourceB380 + difference 0 2) sourceC380) = raw7331 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7331; decide +kernel
    rw [ha]
    exact (canonical7331 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA380 + difference 2 1) (sourceB380 + difference 1 2) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2986) := by
    have ha : (tripleCharges (sourceA380 + difference 2 1) (sourceB380 + difference 1 2) sourceC380) = raw7332 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7332; decide +kernel
    rw [ha]
    exact (canonical7332 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA380 + difference 2 3) (sourceB380 + difference 3 2) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2861) := by
    have ha : (tripleCharges (sourceA380 + difference 2 3) (sourceB380 + difference 3 2) sourceC380) = raw7333 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7333; decide +kernel
    rw [ha]
    exact (canonical7333 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA380 + difference 2 4) (sourceB380 + difference 4 2) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA380 + difference 2 4) (sourceB380 + difference 4 2) sourceC380) = raw7334 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7334; decide +kernel
    rw [ha]
    exact (canonical7334 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA380 + difference 2 5) (sourceB380 + difference 5 2) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA380 + difference 2 5) (sourceB380 + difference 5 2) sourceC380) = raw7335 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7335; decide +kernel
    rw [ha]
    exact (canonical7335 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA380 + difference 3 0) (sourceB380 + difference 0 3) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA380 + difference 3 0) (sourceB380 + difference 0 3) sourceC380) = raw7336 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7336; decide +kernel
    rw [ha]
    exact (canonical7336 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA380 + difference 3 1) (sourceB380 + difference 1 3) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2986) := by
    have ha : (tripleCharges (sourceA380 + difference 3 1) (sourceB380 + difference 1 3) sourceC380) = raw7337 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7337; decide +kernel
    rw [ha]
    exact (canonical7337 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA380 + difference 3 2) (sourceB380 + difference 2 3) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2861) := by
    have ha : (tripleCharges (sourceA380 + difference 3 2) (sourceB380 + difference 2 3) sourceC380) = raw7338 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7338; decide +kernel
    rw [ha]
    exact (canonical7338 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA380 + difference 3 4) (sourceB380 + difference 4 3) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA380 + difference 3 4) (sourceB380 + difference 4 3) sourceC380) = raw7339 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7339; decide +kernel
    rw [ha]
    exact (canonical7339 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA380 + difference 3 5) (sourceB380 + difference 5 3) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA380 + difference 3 5) (sourceB380 + difference 5 3) sourceC380) = raw7340 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7340; decide +kernel
    rw [ha]
    exact (canonical7340 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA380 + difference 4 0) (sourceB380 + difference 0 4) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1196) := by
    have ha : (tripleCharges (sourceA380 + difference 4 0) (sourceB380 + difference 0 4) sourceC380) = raw7341 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7341; decide +kernel
    rw [ha]
    exact (canonical7341 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA380 + difference 4 1) (sourceB380 + difference 1 4) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA380 + difference 4 1) (sourceB380 + difference 1 4) sourceC380) = raw7342 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7342; decide +kernel
    rw [ha]
    exact (canonical7342 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA380 + difference 4 2) (sourceB380 + difference 2 4) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2850) := by
    have ha : (tripleCharges (sourceA380 + difference 4 2) (sourceB380 + difference 2 4) sourceC380) = raw7343 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7343; decide +kernel
    rw [ha]
    exact (canonical7343 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA380 + difference 4 3) (sourceB380 + difference 3 4) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2850) := by
    have ha : (tripleCharges (sourceA380 + difference 4 3) (sourceB380 + difference 3 4) sourceC380) = raw7344 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7344; decide +kernel
    rw [ha]
    exact (canonical7344 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA380 + difference 4 5) (sourceB380 + difference 5 4) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA380 + difference 4 5) (sourceB380 + difference 5 4) sourceC380) = raw7345 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7345; decide +kernel
    rw [ha]
    exact (canonical7345 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA380 + difference 5 0) (sourceB380 + difference 0 5) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1194) := by
    have ha : (tripleCharges (sourceA380 + difference 5 0) (sourceB380 + difference 0 5) sourceC380) = raw7346 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7346; decide +kernel
    rw [ha]
    exact (canonical7346 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA380 + difference 5 1) (sourceB380 + difference 1 5) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA380 + difference 5 1) (sourceB380 + difference 1 5) sourceC380) = raw7347 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7347; decide +kernel
    rw [ha]
    exact (canonical7347 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA380 + difference 5 2) (sourceB380 + difference 2 5) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1988) := by
    have ha : (tripleCharges (sourceA380 + difference 5 2) (sourceB380 + difference 2 5) sourceC380) = raw7348 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7348; decide +kernel
    rw [ha]
    exact (canonical7348 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA380 + difference 5 3) (sourceB380 + difference 3 5) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1988) := by
    have ha : (tripleCharges (sourceA380 + difference 5 3) (sourceB380 + difference 3 5) sourceC380) = raw7349 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7349; decide +kernel
    rw [ha]
    exact (canonical7349 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA380 + difference 5 4) (sourceB380 + difference 4 5) sourceC380) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA380 + difference 5 4) (sourceB380 + difference 4 5) sourceC380) = raw7350 := by
      apply Matrix.ext; unfold tripleCharges sourceA380 sourceB380 sourceC380 difference raw7350; decide +kernel
    rw [ha]
    exact (canonical7350 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA380 sourceB380 sourceC380
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm380, Integer.Sparse.eval]
  linarith only [hs]

def sourceA381 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB381 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC381 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm381 : Integer.Sparse Master := [(Sum.inr 1995, 1), (Sum.inr 1998, 2), (Sum.inr 2050, 1), (Sum.inr 2201, 1), (Sum.inr 3278, 1), (Sum.inr 3280, 1), (Sum.inr 3288, 2), (Sum.inr 3476, 1), (Sum.inr 3477, 2), (Sum.inr 3531, 1), (Sum.inr 3532, 2), (Sum.inr 3536, 2), (Sum.inr 3537, 2), (Sum.inr 3539, 2), (Sum.inr 3571, 1), (Sum.inr 3574, 2), (Sum.inr 3576, 1), (Sum.inr 3812, 1), (Sum.inr 3840, 2), (Sum.inr 3851, 1), (Sum.inr 3855, 1)]

theorem sourceEq381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm381 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA381 + difference 0 1) (sourceB381 + difference 1 0) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA381 + difference 0 1) (sourceB381 + difference 1 0) sourceC381) = raw7351 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7351; decide +kernel
    rw [ha]
    exact (canonical7351 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA381 + difference 0 2) (sourceB381 + difference 2 0) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA381 + difference 0 2) (sourceB381 + difference 2 0) sourceC381) = raw7352 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7352; decide +kernel
    rw [ha]
    exact (canonical7352 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA381 + difference 0 3) (sourceB381 + difference 3 0) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA381 + difference 0 3) (sourceB381 + difference 3 0) sourceC381) = raw7353 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7353; decide +kernel
    rw [ha]
    exact (canonical7353 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA381 + difference 0 4) (sourceB381 + difference 4 0) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3855) := by
    have ha : (tripleCharges (sourceA381 + difference 0 4) (sourceB381 + difference 4 0) sourceC381) = raw7354 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7354; decide +kernel
    rw [ha]
    exact (canonical7354 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA381 + difference 0 5) (sourceB381 + difference 5 0) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA381 + difference 0 5) (sourceB381 + difference 5 0) sourceC381) = raw7355 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7355; decide +kernel
    rw [ha]
    exact (canonical7355 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA381 + difference 1 0) (sourceB381 + difference 0 1) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3278) := by
    have ha : (tripleCharges (sourceA381 + difference 1 0) (sourceB381 + difference 0 1) sourceC381) = raw7356 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7356; decide +kernel
    rw [ha]
    exact (canonical7356 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA381 + difference 1 2) (sourceB381 + difference 2 1) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3574) := by
    have ha : (tripleCharges (sourceA381 + difference 1 2) (sourceB381 + difference 2 1) sourceC381) = raw7357 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7357; decide +kernel
    rw [ha]
    exact (canonical7357 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA381 + difference 1 3) (sourceB381 + difference 3 1) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3574) := by
    have ha : (tripleCharges (sourceA381 + difference 1 3) (sourceB381 + difference 3 1) sourceC381) = raw7358 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7358; decide +kernel
    rw [ha]
    exact (canonical7358 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA381 + difference 1 4) (sourceB381 + difference 4 1) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3576) := by
    have ha : (tripleCharges (sourceA381 + difference 1 4) (sourceB381 + difference 4 1) sourceC381) = raw7359 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7359; decide +kernel
    rw [ha]
    exact (canonical7359 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA381 + difference 1 5) (sourceB381 + difference 5 1) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA381 + difference 1 5) (sourceB381 + difference 5 1) sourceC381) = raw7360 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7360; decide +kernel
    rw [ha]
    exact (canonical7360 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA381 + difference 2 0) (sourceB381 + difference 0 2) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA381 + difference 2 0) (sourceB381 + difference 0 2) sourceC381) = raw7361 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7361; decide +kernel
    rw [ha]
    exact (canonical7361 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA381 + difference 2 1) (sourceB381 + difference 1 2) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA381 + difference 2 1) (sourceB381 + difference 1 2) sourceC381) = raw7362 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7362; decide +kernel
    rw [ha]
    exact (canonical7362 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA381 + difference 2 3) (sourceB381 + difference 3 2) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA381 + difference 2 3) (sourceB381 + difference 3 2) sourceC381) = raw7363 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7363; decide +kernel
    rw [ha]
    exact (canonical7363 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA381 + difference 2 4) (sourceB381 + difference 4 2) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA381 + difference 2 4) (sourceB381 + difference 4 2) sourceC381) = raw7364 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7364; decide +kernel
    rw [ha]
    exact (canonical7364 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA381 + difference 2 5) (sourceB381 + difference 5 2) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA381 + difference 2 5) (sourceB381 + difference 5 2) sourceC381) = raw7365 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7365; decide +kernel
    rw [ha]
    exact (canonical7365 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA381 + difference 3 0) (sourceB381 + difference 0 3) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA381 + difference 3 0) (sourceB381 + difference 0 3) sourceC381) = raw7366 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7366; decide +kernel
    rw [ha]
    exact (canonical7366 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA381 + difference 3 1) (sourceB381 + difference 1 3) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA381 + difference 3 1) (sourceB381 + difference 1 3) sourceC381) = raw7367 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7367; decide +kernel
    rw [ha]
    exact (canonical7367 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA381 + difference 3 2) (sourceB381 + difference 2 3) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA381 + difference 3 2) (sourceB381 + difference 2 3) sourceC381) = raw7368 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7368; decide +kernel
    rw [ha]
    exact (canonical7368 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA381 + difference 3 4) (sourceB381 + difference 4 3) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA381 + difference 3 4) (sourceB381 + difference 4 3) sourceC381) = raw7369 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7369; decide +kernel
    rw [ha]
    exact (canonical7369 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA381 + difference 3 5) (sourceB381 + difference 5 3) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA381 + difference 3 5) (sourceB381 + difference 5 3) sourceC381) = raw7370 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7370; decide +kernel
    rw [ha]
    exact (canonical7370 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA381 + difference 4 0) (sourceB381 + difference 0 4) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3280) := by
    have ha : (tripleCharges (sourceA381 + difference 4 0) (sourceB381 + difference 0 4) sourceC381) = raw7371 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7371; decide +kernel
    rw [ha]
    exact (canonical7371 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA381 + difference 4 1) (sourceB381 + difference 1 4) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA381 + difference 4 1) (sourceB381 + difference 1 4) sourceC381) = raw7372 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7372; decide +kernel
    rw [ha]
    exact (canonical7372 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA381 + difference 4 2) (sourceB381 + difference 2 4) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3536) := by
    have ha : (tripleCharges (sourceA381 + difference 4 2) (sourceB381 + difference 2 4) sourceC381) = raw7373 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7373; decide +kernel
    rw [ha]
    exact (canonical7373 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA381 + difference 4 3) (sourceB381 + difference 3 4) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3536) := by
    have ha : (tripleCharges (sourceA381 + difference 4 3) (sourceB381 + difference 3 4) sourceC381) = raw7374 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7374; decide +kernel
    rw [ha]
    exact (canonical7374 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA381 + difference 4 5) (sourceB381 + difference 5 4) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA381 + difference 4 5) (sourceB381 + difference 5 4) sourceC381) = raw7375 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7375; decide +kernel
    rw [ha]
    exact (canonical7375 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA381 + difference 5 0) (sourceB381 + difference 0 5) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1995) := by
    have ha : (tripleCharges (sourceA381 + difference 5 0) (sourceB381 + difference 0 5) sourceC381) = raw7376 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7376; decide +kernel
    rw [ha]
    exact (canonical7376 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA381 + difference 5 1) (sourceB381 + difference 1 5) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA381 + difference 5 1) (sourceB381 + difference 1 5) sourceC381) = raw7377 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7377; decide +kernel
    rw [ha]
    exact (canonical7377 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA381 + difference 5 2) (sourceB381 + difference 2 5) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1998) := by
    have ha : (tripleCharges (sourceA381 + difference 5 2) (sourceB381 + difference 2 5) sourceC381) = raw7378 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7378; decide +kernel
    rw [ha]
    exact (canonical7378 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA381 + difference 5 3) (sourceB381 + difference 3 5) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1998) := by
    have ha : (tripleCharges (sourceA381 + difference 5 3) (sourceB381 + difference 3 5) sourceC381) = raw7379 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7379; decide +kernel
    rw [ha]
    exact (canonical7379 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA381 + difference 5 4) (sourceB381 + difference 4 5) sourceC381) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA381 + difference 5 4) (sourceB381 + difference 4 5) sourceC381) = raw7380 := by
      apply Matrix.ext; unfold tripleCharges sourceA381 sourceB381 sourceC381 difference raw7380; decide +kernel
    rw [ha]
    exact (canonical7380 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA381 sourceB381 sourceC381
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm381, Integer.Sparse.eval]
  linarith only [hs]

def sourceA382 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB382 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC382 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm382 : Integer.Sparse Master := [(Sum.inr 2710, 1), (Sum.inr 3801, 1), (Sum.inr 3872, 2), (Sum.inr 3899, 1), (Sum.inr 3901, 1), (Sum.inr 4091, -1)]

theorem sourceEq382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm382 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA382 + difference 0 0) (sourceB382 + difference 0 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA382 + difference 0 0) (sourceB382 + difference 0 0) sourceC382) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA382 + difference 0 1) (sourceB382 + difference 1 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA382 + difference 0 1) (sourceB382 + difference 1 0) sourceC382) = raw7382 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7382; decide +kernel
    rw [ha]
    exact (canonical7382 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA382 + difference 0 2) (sourceB382 + difference 2 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA382 + difference 0 2) (sourceB382 + difference 2 0) sourceC382) = raw7383 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7383; decide +kernel
    rw [ha]
    exact (canonical7383 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA382 + difference 0 3) (sourceB382 + difference 3 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA382 + difference 0 3) (sourceB382 + difference 3 0) sourceC382) = raw7384 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7384; decide +kernel
    rw [ha]
    exact (canonical7384 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA382 + difference 0 4) (sourceB382 + difference 4 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA382 + difference 0 4) (sourceB382 + difference 4 0) sourceC382) = raw7385 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7385; decide +kernel
    rw [ha]
    exact (canonical7385 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA382 + difference 0 5) (sourceB382 + difference 5 0) sourceC382) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3901) := by
    have ha : (tripleCharges (sourceA382 + difference 0 5) (sourceB382 + difference 5 0) sourceC382) = raw7386 := by
      apply Matrix.ext; unfold tripleCharges sourceA382 sourceB382 sourceC382 difference raw7386; decide +kernel
    rw [ha]
    exact (canonical7386 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA382 + sourceB382) sourceC382) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA382 + sourceB382) sourceC382) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA382 sourceB382 sourceC382 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA382 sourceB382 sourceC382
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm382, Integer.Sparse.eval]
  linarith only [hs]

def sourceA383 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB383 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC383 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm383 : Integer.Sparse Master := [(Sum.inr 1207, 1), (Sum.inr 1208, 1), (Sum.inr 1216, 2), (Sum.inr 1248, 1), (Sum.inr 2710, 1), (Sum.inr 4091, -1)]

theorem sourceEq383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm383 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA383 + difference 0 0) (sourceB383 + difference 0 0) sourceC383) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA383 + difference 0 0) (sourceB383 + difference 0 0) sourceC383) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA383 sourceB383 sourceC383 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA383 + difference 1 0) (sourceB383 + difference 0 1) sourceC383) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1248) := by
    have ha : (tripleCharges (sourceA383 + difference 1 0) (sourceB383 + difference 0 1) sourceC383) = raw7388 := by
      apply Matrix.ext; unfold tripleCharges sourceA383 sourceB383 sourceC383 difference raw7388; decide +kernel
    rw [ha]
    exact (canonical7388 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA383 + difference 2 0) (sourceB383 + difference 0 2) sourceC383) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA383 + difference 2 0) (sourceB383 + difference 0 2) sourceC383) = raw7389 := by
      apply Matrix.ext; unfold tripleCharges sourceA383 sourceB383 sourceC383 difference raw7389; decide +kernel
    rw [ha]
    exact (canonical7389 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA383 + difference 3 0) (sourceB383 + difference 0 3) sourceC383) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA383 + difference 3 0) (sourceB383 + difference 0 3) sourceC383) = raw7390 := by
      apply Matrix.ext; unfold tripleCharges sourceA383 sourceB383 sourceC383 difference raw7390; decide +kernel
    rw [ha]
    exact (canonical7390 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA383 + difference 4 0) (sourceB383 + difference 0 4) sourceC383) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1208) := by
    have ha : (tripleCharges (sourceA383 + difference 4 0) (sourceB383 + difference 0 4) sourceC383) = raw7391 := by
      apply Matrix.ext; unfold tripleCharges sourceA383 sourceB383 sourceC383 difference raw7391; decide +kernel
    rw [ha]
    exact (canonical7391 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA383 + difference 5 0) (sourceB383 + difference 0 5) sourceC383) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1207) := by
    have ha : (tripleCharges (sourceA383 + difference 5 0) (sourceB383 + difference 0 5) sourceC383) = raw7392 := by
      apply Matrix.ext; unfold tripleCharges sourceA383 sourceB383 sourceC383 difference raw7392; decide +kernel
    rw [ha]
    exact (canonical7392 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA383 + sourceB383) sourceC383) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA383 + sourceB383) sourceC383) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA383 sourceB383 sourceC383 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA383 sourceB383 sourceC383
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm383, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
