import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical95
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical105
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical107
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical108
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical110
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical111
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical112

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA832 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB832 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC832 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceForm832 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 1213, 2), (Sum.inr 1233, 1), (Sum.inr 1265, 1), (Sum.inr 2861, 1), (Sum.inr 2862, 2), (Sum.inr 2878, 1), (Sum.inr 2986, 1), (Sum.inr 2987, 2), (Sum.inr 2999, 1), (Sum.inr 3064, 2), (Sum.inr 3065, 2), (Sum.inr 3074, 2), (Sum.inr 3087, 2), (Sum.inr 3088, 2), (Sum.inr 3099, 1), (Sum.inr 3111, 1), (Sum.inr 4026, 1), (Sum.inr 4033, 2), (Sum.inr 4036, 1), (Sum.inr 4038, 1)]

theorem sourceEq832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm832 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA832 + difference 0 1) (sourceB832 + difference 1 0) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA832 + difference 0 1) (sourceB832 + difference 1 0) sourceC832) = raw13703 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13703; decide +kernel
    rw [ha]
    exact (canonical13703 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA832 + difference 0 2) (sourceB832 + difference 2 0) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4038) := by
    have ha : (tripleCharges (sourceA832 + difference 0 2) (sourceB832 + difference 2 0) sourceC832) = raw13704 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13704; decide +kernel
    rw [ha]
    exact (canonical13704 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA832 + difference 0 3) (sourceB832 + difference 3 0) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA832 + difference 0 3) (sourceB832 + difference 3 0) sourceC832) = raw13705 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13705; decide +kernel
    rw [ha]
    exact (canonical13705 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA832 + difference 0 4) (sourceB832 + difference 4 0) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA832 + difference 0 4) (sourceB832 + difference 4 0) sourceC832) = raw13706 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13706; decide +kernel
    rw [ha]
    exact (canonical13706 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA832 + difference 0 5) (sourceB832 + difference 5 0) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4036) := by
    have ha : (tripleCharges (sourceA832 + difference 0 5) (sourceB832 + difference 5 0) sourceC832) = raw13707 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13707; decide +kernel
    rw [ha]
    exact (canonical13707 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA832 + difference 1 0) (sourceB832 + difference 0 1) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1265) := by
    have ha : (tripleCharges (sourceA832 + difference 1 0) (sourceB832 + difference 0 1) sourceC832) = raw13708 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13708; decide +kernel
    rw [ha]
    exact (canonical13708 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA832 + difference 1 2) (sourceB832 + difference 2 1) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2999) := by
    have ha : (tripleCharges (sourceA832 + difference 1 2) (sourceB832 + difference 2 1) sourceC832) = raw13709 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13709; decide +kernel
    rw [ha]
    exact (canonical13709 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA832 + difference 1 3) (sourceB832 + difference 3 1) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA832 + difference 1 3) (sourceB832 + difference 3 1) sourceC832) = raw13710 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13710; decide +kernel
    rw [ha]
    exact (canonical13710 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA832 + difference 1 4) (sourceB832 + difference 4 1) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA832 + difference 1 4) (sourceB832 + difference 4 1) sourceC832) = raw13711 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13711; decide +kernel
    rw [ha]
    exact (canonical13711 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA832 + difference 1 5) (sourceB832 + difference 5 1) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3111) := by
    have ha : (tripleCharges (sourceA832 + difference 1 5) (sourceB832 + difference 5 1) sourceC832) = raw13712 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13712; decide +kernel
    rw [ha]
    exact (canonical13712 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA832 + difference 2 0) (sourceB832 + difference 0 2) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA832 + difference 2 0) (sourceB832 + difference 0 2) sourceC832) = raw13713 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13713; decide +kernel
    rw [ha]
    exact (canonical13713 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA832 + difference 2 1) (sourceB832 + difference 1 2) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA832 + difference 2 1) (sourceB832 + difference 1 2) sourceC832) = raw13714 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13714; decide +kernel
    rw [ha]
    exact (canonical13714 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA832 + difference 2 3) (sourceB832 + difference 3 2) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA832 + difference 2 3) (sourceB832 + difference 3 2) sourceC832) = raw13715 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13715; decide +kernel
    rw [ha]
    exact (canonical13715 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA832 + difference 2 4) (sourceB832 + difference 4 2) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA832 + difference 2 4) (sourceB832 + difference 4 2) sourceC832) = raw13716 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13716; decide +kernel
    rw [ha]
    exact (canonical13716 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA832 + difference 2 5) (sourceB832 + difference 5 2) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA832 + difference 2 5) (sourceB832 + difference 5 2) sourceC832) = raw13717 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13717; decide +kernel
    rw [ha]
    exact (canonical13717 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA832 + difference 3 0) (sourceB832 + difference 0 3) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA832 + difference 3 0) (sourceB832 + difference 0 3) sourceC832) = raw13718 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13718; decide +kernel
    rw [ha]
    exact (canonical13718 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA832 + difference 3 1) (sourceB832 + difference 1 3) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA832 + difference 3 1) (sourceB832 + difference 1 3) sourceC832) = raw13719 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13719; decide +kernel
    rw [ha]
    exact (canonical13719 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA832 + difference 3 2) (sourceB832 + difference 2 3) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2987) := by
    have ha : (tripleCharges (sourceA832 + difference 3 2) (sourceB832 + difference 2 3) sourceC832) = raw13720 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13720; decide +kernel
    rw [ha]
    exact (canonical13720 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA832 + difference 3 4) (sourceB832 + difference 4 3) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA832 + difference 3 4) (sourceB832 + difference 4 3) sourceC832) = raw13721 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13721; decide +kernel
    rw [ha]
    exact (canonical13721 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA832 + difference 3 5) (sourceB832 + difference 5 3) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA832 + difference 3 5) (sourceB832 + difference 5 3) sourceC832) = raw13722 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13722; decide +kernel
    rw [ha]
    exact (canonical13722 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA832 + difference 4 0) (sourceB832 + difference 0 4) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA832 + difference 4 0) (sourceB832 + difference 0 4) sourceC832) = raw13723 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13723; decide +kernel
    rw [ha]
    exact (canonical13723 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA832 + difference 4 1) (sourceB832 + difference 1 4) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA832 + difference 4 1) (sourceB832 + difference 1 4) sourceC832) = raw13724 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13724; decide +kernel
    rw [ha]
    exact (canonical13724 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA832 + difference 4 2) (sourceB832 + difference 2 4) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2987) := by
    have ha : (tripleCharges (sourceA832 + difference 4 2) (sourceB832 + difference 2 4) sourceC832) = raw13725 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13725; decide +kernel
    rw [ha]
    exact (canonical13725 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA832 + difference 4 3) (sourceB832 + difference 3 4) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA832 + difference 4 3) (sourceB832 + difference 3 4) sourceC832) = raw13726 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13726; decide +kernel
    rw [ha]
    exact (canonical13726 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA832 + difference 4 5) (sourceB832 + difference 5 4) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA832 + difference 4 5) (sourceB832 + difference 5 4) sourceC832) = raw13727 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13727; decide +kernel
    rw [ha]
    exact (canonical13727 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA832 + difference 5 0) (sourceB832 + difference 0 5) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA832 + difference 5 0) (sourceB832 + difference 0 5) sourceC832) = raw13728 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13728; decide +kernel
    rw [ha]
    exact (canonical13728 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA832 + difference 5 1) (sourceB832 + difference 1 5) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2861) := by
    have ha : (tripleCharges (sourceA832 + difference 5 1) (sourceB832 + difference 1 5) sourceC832) = raw13729 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13729; decide +kernel
    rw [ha]
    exact (canonical13729 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA832 + difference 5 2) (sourceB832 + difference 2 5) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2986) := by
    have ha : (tripleCharges (sourceA832 + difference 5 2) (sourceB832 + difference 2 5) sourceC832) = raw13730 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13730; decide +kernel
    rw [ha]
    exact (canonical13730 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA832 + difference 5 3) (sourceB832 + difference 3 5) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA832 + difference 5 3) (sourceB832 + difference 3 5) sourceC832) = raw13731 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13731; decide +kernel
    rw [ha]
    exact (canonical13731 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA832 + difference 5 4) (sourceB832 + difference 4 5) sourceC832) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA832 + difference 5 4) (sourceB832 + difference 4 5) sourceC832) = raw13732 := by
      apply Matrix.ext; unfold tripleCharges sourceA832 sourceB832 sourceC832 difference raw13732; decide +kernel
    rw [ha]
    exact (canonical13732 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA832 sourceB832 sourceC832
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm832, Integer.Sparse.eval]
  linarith only [hs]

def sourceA833 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB833 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC833 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceForm833 : Integer.Sparse Master := [(Sum.inr 3288, 1), (Sum.inr 3289, 1), (Sum.inr 3290, 2), (Sum.inr 3292, 1), (Sum.inr 3467, 2), (Sum.inr 3469, 1), (Sum.inr 3477, 1), (Sum.inr 3529, 2), (Sum.inr 3531, 2), (Sum.inr 3532, 2), (Sum.inr 3537, 1), (Sum.inr 3539, 2), (Sum.inr 3544, 2), (Sum.inr 3546, 1), (Sum.inr 3569, 1), (Sum.inr 3571, 2), (Sum.inr 3581, 1), (Sum.inr 3806, 1), (Sum.inr 3849, 1), (Sum.inr 3851, 2), (Sum.inr 3859, 1)]

theorem sourceEq833 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm833 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA833 + difference 0 1) (sourceB833 + difference 1 0) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA833 + difference 0 1) (sourceB833 + difference 1 0) sourceC833) = raw13733 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13733; decide +kernel
    rw [ha]
    exact (canonical13733 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA833 + difference 0 2) (sourceB833 + difference 2 0) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA833 + difference 0 2) (sourceB833 + difference 2 0) sourceC833) = raw13734 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13734; decide +kernel
    rw [ha]
    exact (canonical13734 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA833 + difference 0 3) (sourceB833 + difference 3 0) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA833 + difference 0 3) (sourceB833 + difference 3 0) sourceC833) = raw13735 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13735; decide +kernel
    rw [ha]
    exact (canonical13735 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA833 + difference 0 4) (sourceB833 + difference 4 0) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA833 + difference 0 4) (sourceB833 + difference 4 0) sourceC833) = raw13736 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13736; decide +kernel
    rw [ha]
    exact (canonical13736 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA833 + difference 0 5) (sourceB833 + difference 5 0) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3859) := by
    have ha : (tripleCharges (sourceA833 + difference 0 5) (sourceB833 + difference 5 0) sourceC833) = raw13737 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13737; decide +kernel
    rw [ha]
    exact (canonical13737 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA833 + difference 1 0) (sourceB833 + difference 0 1) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA833 + difference 1 0) (sourceB833 + difference 0 1) sourceC833) = raw13738 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13738; decide +kernel
    rw [ha]
    exact (canonical13738 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA833 + difference 1 2) (sourceB833 + difference 2 1) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3469) := by
    have ha : (tripleCharges (sourceA833 + difference 1 2) (sourceB833 + difference 2 1) sourceC833) = raw13739 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13739; decide +kernel
    rw [ha]
    exact (canonical13739 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA833 + difference 1 3) (sourceB833 + difference 3 1) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA833 + difference 1 3) (sourceB833 + difference 3 1) sourceC833) = raw13740 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13740; decide +kernel
    rw [ha]
    exact (canonical13740 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA833 + difference 1 4) (sourceB833 + difference 4 1) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA833 + difference 1 4) (sourceB833 + difference 4 1) sourceC833) = raw13741 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13741; decide +kernel
    rw [ha]
    exact (canonical13741 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA833 + difference 1 5) (sourceB833 + difference 5 1) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA833 + difference 1 5) (sourceB833 + difference 5 1) sourceC833) = raw13742 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13742; decide +kernel
    rw [ha]
    exact (canonical13742 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA833 + difference 2 0) (sourceB833 + difference 0 2) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA833 + difference 2 0) (sourceB833 + difference 0 2) sourceC833) = raw13743 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13743; decide +kernel
    rw [ha]
    exact (canonical13743 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA833 + difference 2 1) (sourceB833 + difference 1 2) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA833 + difference 2 1) (sourceB833 + difference 1 2) sourceC833) = raw13744 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13744; decide +kernel
    rw [ha]
    exact (canonical13744 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA833 + difference 2 3) (sourceB833 + difference 3 2) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA833 + difference 2 3) (sourceB833 + difference 3 2) sourceC833) = raw13745 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13745; decide +kernel
    rw [ha]
    exact (canonical13745 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA833 + difference 2 4) (sourceB833 + difference 4 2) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA833 + difference 2 4) (sourceB833 + difference 4 2) sourceC833) = raw13746 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13746; decide +kernel
    rw [ha]
    exact (canonical13746 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA833 + difference 2 5) (sourceB833 + difference 5 2) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA833 + difference 2 5) (sourceB833 + difference 5 2) sourceC833) = raw13747 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13747; decide +kernel
    rw [ha]
    exact (canonical13747 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA833 + difference 3 0) (sourceB833 + difference 0 3) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA833 + difference 3 0) (sourceB833 + difference 0 3) sourceC833) = raw13748 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13748; decide +kernel
    rw [ha]
    exact (canonical13748 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA833 + difference 3 1) (sourceB833 + difference 1 3) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA833 + difference 3 1) (sourceB833 + difference 1 3) sourceC833) = raw13749 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13749; decide +kernel
    rw [ha]
    exact (canonical13749 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA833 + difference 3 2) (sourceB833 + difference 2 3) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA833 + difference 3 2) (sourceB833 + difference 2 3) sourceC833) = raw13750 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13750; decide +kernel
    rw [ha]
    exact (canonical13750 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA833 + difference 3 4) (sourceB833 + difference 4 3) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA833 + difference 3 4) (sourceB833 + difference 4 3) sourceC833) = raw13751 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13751; decide +kernel
    rw [ha]
    exact (canonical13751 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA833 + difference 3 5) (sourceB833 + difference 5 3) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA833 + difference 3 5) (sourceB833 + difference 5 3) sourceC833) = raw13752 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13752; decide +kernel
    rw [ha]
    exact (canonical13752 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA833 + difference 4 0) (sourceB833 + difference 0 4) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA833 + difference 4 0) (sourceB833 + difference 0 4) sourceC833) = raw13753 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13753; decide +kernel
    rw [ha]
    exact (canonical13753 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA833 + difference 4 1) (sourceB833 + difference 1 4) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA833 + difference 4 1) (sourceB833 + difference 1 4) sourceC833) = raw13754 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13754; decide +kernel
    rw [ha]
    exact (canonical13754 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA833 + difference 4 2) (sourceB833 + difference 2 4) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA833 + difference 4 2) (sourceB833 + difference 2 4) sourceC833) = raw13755 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13755; decide +kernel
    rw [ha]
    exact (canonical13755 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA833 + difference 4 3) (sourceB833 + difference 3 4) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA833 + difference 4 3) (sourceB833 + difference 3 4) sourceC833) = raw13756 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13756; decide +kernel
    rw [ha]
    exact (canonical13756 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA833 + difference 4 5) (sourceB833 + difference 5 4) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA833 + difference 4 5) (sourceB833 + difference 5 4) sourceC833) = raw13757 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13757; decide +kernel
    rw [ha]
    exact (canonical13757 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA833 + difference 5 0) (sourceB833 + difference 0 5) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA833 + difference 5 0) (sourceB833 + difference 0 5) sourceC833) = raw13758 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13758; decide +kernel
    rw [ha]
    exact (canonical13758 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA833 + difference 5 1) (sourceB833 + difference 1 5) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA833 + difference 5 1) (sourceB833 + difference 1 5) sourceC833) = raw13759 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13759; decide +kernel
    rw [ha]
    exact (canonical13759 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA833 + difference 5 2) (sourceB833 + difference 2 5) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA833 + difference 5 2) (sourceB833 + difference 2 5) sourceC833) = raw13760 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13760; decide +kernel
    rw [ha]
    exact (canonical13760 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA833 + difference 5 3) (sourceB833 + difference 3 5) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA833 + difference 5 3) (sourceB833 + difference 3 5) sourceC833) = raw13761 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13761; decide +kernel
    rw [ha]
    exact (canonical13761 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA833 + difference 5 4) (sourceB833 + difference 4 5) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA833 + difference 5 4) (sourceB833 + difference 4 5) sourceC833) = raw13762 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13762; decide +kernel
    rw [ha]
    exact (canonical13762 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA833 sourceB833 sourceC833
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm833, Integer.Sparse.eval]
  linarith only [hs]

def sourceA834 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB834 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC834 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceForm834 : Integer.Sparse Master := [(Sum.inr 1235, 1), (Sum.inr 2510, 1), (Sum.inr 2721, 3), (Sum.inr 2741, 1), (Sum.inr 4091, -1)]

theorem sourceEq834 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm834 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA834 + difference 1 0) (sourceB834 + difference 0 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA834 + difference 1 0) (sourceB834 + difference 0 1) sourceC834) = raw13763 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13763; decide +kernel
    rw [ha]
    exact (canonical13763 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA834 + difference 1 1) (sourceB834 + difference 1 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA834 + difference 1 1) (sourceB834 + difference 1 1) sourceC834) = raw13764 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13764; decide +kernel
    rw [ha]
    exact (canonical13764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA834 + difference 1 2) (sourceB834 + difference 2 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2510) := by
    have ha : (tripleCharges (sourceA834 + difference 1 2) (sourceB834 + difference 2 1) sourceC834) = raw13765 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13765; decide +kernel
    rw [ha]
    exact (canonical13765 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA834 + difference 1 3) (sourceB834 + difference 3 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA834 + difference 1 3) (sourceB834 + difference 3 1) sourceC834) = raw13766 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13766; decide +kernel
    rw [ha]
    exact (canonical13766 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA834 + difference 1 4) (sourceB834 + difference 4 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA834 + difference 1 4) (sourceB834 + difference 4 1) sourceC834) = raw13767 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13767; decide +kernel
    rw [ha]
    exact (canonical13767 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA834 + difference 1 5) (sourceB834 + difference 5 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA834 + difference 1 5) (sourceB834 + difference 5 1) sourceC834) = raw13768 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13768; decide +kernel
    rw [ha]
    exact (canonical13768 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA834 + sourceB834) sourceC834) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA834 + sourceB834) sourceC834) = raw13769 := by
      apply Matrix.ext; unfold doubleCharges sourceA834 sourceB834 sourceC834 raw13769; decide +kernel
    rw [ha]
    exact (canonical13769 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA834 sourceB834 sourceC834
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm834, Integer.Sparse.eval]
  linarith only [hs]

def sourceA835 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB835 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC835 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceForm835 : Integer.Sparse Master := [(Sum.inr 2615, 2), (Sum.inr 2617, 1), (Sum.inr 2631, 1), (Sum.inr 2721, 1), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

theorem sourceEq835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm835 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA835 + difference 0 1) (sourceB835 + difference 1 0) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA835 + difference 0 1) (sourceB835 + difference 1 0) sourceC835) = raw13770 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13770; decide +kernel
    rw [ha]
    exact (canonical13770 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA835 + difference 1 1) (sourceB835 + difference 1 1) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA835 + difference 1 1) (sourceB835 + difference 1 1) sourceC835) = raw13764 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13764; decide +kernel
    rw [ha]
    exact (canonical13764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA835 + difference 2 1) (sourceB835 + difference 1 2) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA835 + difference 2 1) (sourceB835 + difference 1 2) sourceC835) = raw13771 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13771; decide +kernel
    rw [ha]
    exact (canonical13771 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA835 + difference 3 1) (sourceB835 + difference 1 3) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA835 + difference 3 1) (sourceB835 + difference 1 3) sourceC835) = raw13772 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13772; decide +kernel
    rw [ha]
    exact (canonical13772 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA835 + difference 4 1) (sourceB835 + difference 1 4) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA835 + difference 4 1) (sourceB835 + difference 1 4) sourceC835) = raw13773 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13773; decide +kernel
    rw [ha]
    exact (canonical13773 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA835 + difference 5 1) (sourceB835 + difference 1 5) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA835 + difference 5 1) (sourceB835 + difference 1 5) sourceC835) = raw13774 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13774; decide +kernel
    rw [ha]
    exact (canonical13774 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA835 + sourceB835) sourceC835) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA835 + sourceB835) sourceC835) = raw13769 := by
      apply Matrix.ext; unfold doubleCharges sourceA835 sourceB835 sourceC835 raw13769; decide +kernel
    rw [ha]
    exact (canonical13769 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA835 sourceB835 sourceC835
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm835, Integer.Sparse.eval]
  linarith only [hs]

def sourceA836 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB836 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC836 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceForm836 : Integer.Sparse Master := [(Sum.inr 4396, 2), (Sum.inr 4399, 1), (Sum.inr 4417, 1), (Sum.inr 4456, 1), (Sum.inr 4996, 2), (Sum.inr 4998, 1), (Sum.inr 5013, 1), (Sum.inr 5134, 2), (Sum.inr 5137, 1), (Sum.inr 5167, 1), (Sum.inr 5241, 2), (Sum.inr 5247, 1), (Sum.inr 5257, 1), (Sum.inr 5258, 2), (Sum.inr 5259, 2), (Sum.inr 5271, 2), (Sum.inr 5292, 2), (Sum.inr 5472, 1), (Sum.inr 5482, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2)]

theorem sourceEq836 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm836 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA836 + difference 0 1) (sourceB836 + difference 1 0) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA836 + difference 0 1) (sourceB836 + difference 1 0) sourceC836) = raw13775 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13775; decide +kernel
    rw [ha]
    exact (canonical13775 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA836 + difference 0 2) (sourceB836 + difference 2 0) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA836 + difference 0 2) (sourceB836 + difference 2 0) sourceC836) = raw13776 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13776; decide +kernel
    rw [ha]
    exact (canonical13776 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA836 + difference 0 3) (sourceB836 + difference 3 0) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA836 + difference 0 3) (sourceB836 + difference 3 0) sourceC836) = raw13777 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13777; decide +kernel
    rw [ha]
    exact (canonical13777 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA836 + difference 0 4) (sourceB836 + difference 4 0) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA836 + difference 0 4) (sourceB836 + difference 4 0) sourceC836) = raw13778 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13778; decide +kernel
    rw [ha]
    exact (canonical13778 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA836 + difference 0 5) (sourceB836 + difference 5 0) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA836 + difference 0 5) (sourceB836 + difference 5 0) sourceC836) = raw13779 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13779; decide +kernel
    rw [ha]
    exact (canonical13779 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA836 + difference 1 0) (sourceB836 + difference 0 1) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA836 + difference 1 0) (sourceB836 + difference 0 1) sourceC836) = raw13780 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13780; decide +kernel
    rw [ha]
    exact (canonical13780 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA836 + difference 1 2) (sourceB836 + difference 2 1) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA836 + difference 1 2) (sourceB836 + difference 2 1) sourceC836) = raw13781 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13781; decide +kernel
    rw [ha]
    exact (canonical13781 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA836 + difference 1 3) (sourceB836 + difference 3 1) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA836 + difference 1 3) (sourceB836 + difference 3 1) sourceC836) = raw13782 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13782; decide +kernel
    rw [ha]
    exact (canonical13782 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA836 + difference 1 4) (sourceB836 + difference 4 1) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA836 + difference 1 4) (sourceB836 + difference 4 1) sourceC836) = raw13783 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13783; decide +kernel
    rw [ha]
    exact (canonical13783 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA836 + difference 1 5) (sourceB836 + difference 5 1) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA836 + difference 1 5) (sourceB836 + difference 5 1) sourceC836) = raw13784 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13784; decide +kernel
    rw [ha]
    exact (canonical13784 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA836 + difference 2 0) (sourceB836 + difference 0 2) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA836 + difference 2 0) (sourceB836 + difference 0 2) sourceC836) = raw13785 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13785; decide +kernel
    rw [ha]
    exact (canonical13785 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA836 + difference 2 1) (sourceB836 + difference 1 2) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA836 + difference 2 1) (sourceB836 + difference 1 2) sourceC836) = raw13786 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13786; decide +kernel
    rw [ha]
    exact (canonical13786 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA836 + difference 2 3) (sourceB836 + difference 3 2) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA836 + difference 2 3) (sourceB836 + difference 3 2) sourceC836) = raw13787 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13787; decide +kernel
    rw [ha]
    exact (canonical13787 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA836 + difference 2 4) (sourceB836 + difference 4 2) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA836 + difference 2 4) (sourceB836 + difference 4 2) sourceC836) = raw13788 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13788; decide +kernel
    rw [ha]
    exact (canonical13788 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA836 + difference 2 5) (sourceB836 + difference 5 2) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA836 + difference 2 5) (sourceB836 + difference 5 2) sourceC836) = raw13789 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13789; decide +kernel
    rw [ha]
    exact (canonical13789 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA836 + difference 3 0) (sourceB836 + difference 0 3) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA836 + difference 3 0) (sourceB836 + difference 0 3) sourceC836) = raw13790 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13790; decide +kernel
    rw [ha]
    exact (canonical13790 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA836 + difference 3 1) (sourceB836 + difference 1 3) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA836 + difference 3 1) (sourceB836 + difference 1 3) sourceC836) = raw13791 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13791; decide +kernel
    rw [ha]
    exact (canonical13791 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA836 + difference 3 2) (sourceB836 + difference 2 3) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA836 + difference 3 2) (sourceB836 + difference 2 3) sourceC836) = raw13792 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13792; decide +kernel
    rw [ha]
    exact (canonical13792 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA836 + difference 3 4) (sourceB836 + difference 4 3) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA836 + difference 3 4) (sourceB836 + difference 4 3) sourceC836) = raw13793 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13793; decide +kernel
    rw [ha]
    exact (canonical13793 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA836 + difference 3 5) (sourceB836 + difference 5 3) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA836 + difference 3 5) (sourceB836 + difference 5 3) sourceC836) = raw13794 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13794; decide +kernel
    rw [ha]
    exact (canonical13794 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA836 + difference 4 0) (sourceB836 + difference 0 4) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA836 + difference 4 0) (sourceB836 + difference 0 4) sourceC836) = raw13795 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13795; decide +kernel
    rw [ha]
    exact (canonical13795 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA836 + difference 4 1) (sourceB836 + difference 1 4) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA836 + difference 4 1) (sourceB836 + difference 1 4) sourceC836) = raw13796 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13796; decide +kernel
    rw [ha]
    exact (canonical13796 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA836 + difference 4 2) (sourceB836 + difference 2 4) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA836 + difference 4 2) (sourceB836 + difference 2 4) sourceC836) = raw13797 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13797; decide +kernel
    rw [ha]
    exact (canonical13797 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA836 + difference 4 3) (sourceB836 + difference 3 4) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA836 + difference 4 3) (sourceB836 + difference 3 4) sourceC836) = raw13798 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13798; decide +kernel
    rw [ha]
    exact (canonical13798 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA836 + difference 4 5) (sourceB836 + difference 5 4) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA836 + difference 4 5) (sourceB836 + difference 5 4) sourceC836) = raw13799 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13799; decide +kernel
    rw [ha]
    exact (canonical13799 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA836 + difference 5 0) (sourceB836 + difference 0 5) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA836 + difference 5 0) (sourceB836 + difference 0 5) sourceC836) = raw13800 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13800; decide +kernel
    rw [ha]
    exact (canonical13800 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA836 + difference 5 1) (sourceB836 + difference 1 5) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA836 + difference 5 1) (sourceB836 + difference 1 5) sourceC836) = raw13801 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13801; decide +kernel
    rw [ha]
    exact (canonical13801 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA836 + difference 5 2) (sourceB836 + difference 2 5) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA836 + difference 5 2) (sourceB836 + difference 2 5) sourceC836) = raw13802 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13802; decide +kernel
    rw [ha]
    exact (canonical13802 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA836 + difference 5 3) (sourceB836 + difference 3 5) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA836 + difference 5 3) (sourceB836 + difference 3 5) sourceC836) = raw13803 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13803; decide +kernel
    rw [ha]
    exact (canonical13803 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA836 + difference 5 4) (sourceB836 + difference 4 5) sourceC836) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA836 + difference 5 4) (sourceB836 + difference 4 5) sourceC836) = raw13804 := by
      apply Matrix.ext; unfold tripleCharges sourceA836 sourceB836 sourceC836 difference raw13804; decide +kernel
    rw [ha]
    exact (canonical13804 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA836 sourceB836 sourceC836
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm836, Integer.Sparse.eval]
  linarith only [hs]

def sourceA837 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB837 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC837 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceForm837 : Integer.Sparse Master := [(Sum.inr 977, 2), (Sum.inr 980, 1), (Sum.inr 998, 1), (Sum.inr 1039, 1), (Sum.inr 2382, 2), (Sum.inr 2383, 1), (Sum.inr 2398, 1), (Sum.inr 2553, 2), (Sum.inr 2556, 1), (Sum.inr 2593, 1), (Sum.inr 2694, 2), (Sum.inr 2703, 1), (Sum.inr 2721, 1), (Sum.inr 2722, 2), (Sum.inr 2723, 2), (Sum.inr 2739, 2), (Sum.inr 2766, 2), (Sum.inr 3957, 1), (Sum.inr 3992, 1), (Sum.inr 4009, 1), (Sum.inr 4013, 2)]

theorem sourceEq837 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm837 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA837 + difference 0 1) (sourceB837 + difference 1 0) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA837 + difference 0 1) (sourceB837 + difference 1 0) sourceC837) = raw13805 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13805; decide +kernel
    rw [ha]
    exact (canonical13805 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA837 + difference 0 2) (sourceB837 + difference 2 0) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA837 + difference 0 2) (sourceB837 + difference 2 0) sourceC837) = raw13806 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13806; decide +kernel
    rw [ha]
    exact (canonical13806 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA837 + difference 0 3) (sourceB837 + difference 3 0) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA837 + difference 0 3) (sourceB837 + difference 3 0) sourceC837) = raw13807 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13807; decide +kernel
    rw [ha]
    exact (canonical13807 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA837 + difference 0 4) (sourceB837 + difference 4 0) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA837 + difference 0 4) (sourceB837 + difference 4 0) sourceC837) = raw13808 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13808; decide +kernel
    rw [ha]
    exact (canonical13808 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA837 + difference 0 5) (sourceB837 + difference 5 0) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4009) := by
    have ha : (tripleCharges (sourceA837 + difference 0 5) (sourceB837 + difference 5 0) sourceC837) = raw13809 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13809; decide +kernel
    rw [ha]
    exact (canonical13809 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA837 + difference 1 0) (sourceB837 + difference 0 1) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA837 + difference 1 0) (sourceB837 + difference 0 1) sourceC837) = raw13810 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13810; decide +kernel
    rw [ha]
    exact (canonical13810 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA837 + difference 1 2) (sourceB837 + difference 2 1) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2398) := by
    have ha : (tripleCharges (sourceA837 + difference 1 2) (sourceB837 + difference 2 1) sourceC837) = raw13811 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13811; decide +kernel
    rw [ha]
    exact (canonical13811 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA837 + difference 1 3) (sourceB837 + difference 3 1) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA837 + difference 1 3) (sourceB837 + difference 3 1) sourceC837) = raw13812 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13812; decide +kernel
    rw [ha]
    exact (canonical13812 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA837 + difference 1 4) (sourceB837 + difference 4 1) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA837 + difference 1 4) (sourceB837 + difference 4 1) sourceC837) = raw13813 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13813; decide +kernel
    rw [ha]
    exact (canonical13813 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA837 + difference 1 5) (sourceB837 + difference 5 1) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA837 + difference 1 5) (sourceB837 + difference 5 1) sourceC837) = raw13814 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13814; decide +kernel
    rw [ha]
    exact (canonical13814 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA837 + difference 2 0) (sourceB837 + difference 0 2) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA837 + difference 2 0) (sourceB837 + difference 0 2) sourceC837) = raw13815 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13815; decide +kernel
    rw [ha]
    exact (canonical13815 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA837 + difference 2 1) (sourceB837 + difference 1 2) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2593) := by
    have ha : (tripleCharges (sourceA837 + difference 2 1) (sourceB837 + difference 1 2) sourceC837) = raw13816 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13816; decide +kernel
    rw [ha]
    exact (canonical13816 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA837 + difference 2 3) (sourceB837 + difference 3 2) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA837 + difference 2 3) (sourceB837 + difference 3 2) sourceC837) = raw13817 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13817; decide +kernel
    rw [ha]
    exact (canonical13817 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA837 + difference 2 4) (sourceB837 + difference 4 2) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA837 + difference 2 4) (sourceB837 + difference 4 2) sourceC837) = raw13818 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13818; decide +kernel
    rw [ha]
    exact (canonical13818 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA837 + difference 2 5) (sourceB837 + difference 5 2) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA837 + difference 2 5) (sourceB837 + difference 5 2) sourceC837) = raw13819 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13819; decide +kernel
    rw [ha]
    exact (canonical13819 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA837 + difference 3 0) (sourceB837 + difference 0 3) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA837 + difference 3 0) (sourceB837 + difference 0 3) sourceC837) = raw13820 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13820; decide +kernel
    rw [ha]
    exact (canonical13820 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA837 + difference 3 1) (sourceB837 + difference 1 3) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA837 + difference 3 1) (sourceB837 + difference 1 3) sourceC837) = raw13821 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13821; decide +kernel
    rw [ha]
    exact (canonical13821 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA837 + difference 3 2) (sourceB837 + difference 2 3) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA837 + difference 3 2) (sourceB837 + difference 2 3) sourceC837) = raw13822 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13822; decide +kernel
    rw [ha]
    exact (canonical13822 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA837 + difference 3 4) (sourceB837 + difference 4 3) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA837 + difference 3 4) (sourceB837 + difference 4 3) sourceC837) = raw13823 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13823; decide +kernel
    rw [ha]
    exact (canonical13823 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA837 + difference 3 5) (sourceB837 + difference 5 3) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA837 + difference 3 5) (sourceB837 + difference 5 3) sourceC837) = raw13824 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13824; decide +kernel
    rw [ha]
    exact (canonical13824 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA837 + difference 4 0) (sourceB837 + difference 0 4) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA837 + difference 4 0) (sourceB837 + difference 0 4) sourceC837) = raw13825 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13825; decide +kernel
    rw [ha]
    exact (canonical13825 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA837 + difference 4 1) (sourceB837 + difference 1 4) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA837 + difference 4 1) (sourceB837 + difference 1 4) sourceC837) = raw13826 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13826; decide +kernel
    rw [ha]
    exact (canonical13826 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA837 + difference 4 2) (sourceB837 + difference 2 4) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA837 + difference 4 2) (sourceB837 + difference 2 4) sourceC837) = raw13827 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13827; decide +kernel
    rw [ha]
    exact (canonical13827 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA837 + difference 4 3) (sourceB837 + difference 3 4) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA837 + difference 4 3) (sourceB837 + difference 3 4) sourceC837) = raw13828 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13828; decide +kernel
    rw [ha]
    exact (canonical13828 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA837 + difference 4 5) (sourceB837 + difference 5 4) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA837 + difference 4 5) (sourceB837 + difference 5 4) sourceC837) = raw13829 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13829; decide +kernel
    rw [ha]
    exact (canonical13829 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA837 + difference 5 0) (sourceB837 + difference 0 5) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA837 + difference 5 0) (sourceB837 + difference 0 5) sourceC837) = raw13830 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13830; decide +kernel
    rw [ha]
    exact (canonical13830 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA837 + difference 5 1) (sourceB837 + difference 1 5) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA837 + difference 5 1) (sourceB837 + difference 1 5) sourceC837) = raw13831 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13831; decide +kernel
    rw [ha]
    exact (canonical13831 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA837 + difference 5 2) (sourceB837 + difference 2 5) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2383) := by
    have ha : (tripleCharges (sourceA837 + difference 5 2) (sourceB837 + difference 2 5) sourceC837) = raw13832 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13832; decide +kernel
    rw [ha]
    exact (canonical13832 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA837 + difference 5 3) (sourceB837 + difference 3 5) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA837 + difference 5 3) (sourceB837 + difference 3 5) sourceC837) = raw13833 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13833; decide +kernel
    rw [ha]
    exact (canonical13833 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA837 + difference 5 4) (sourceB837 + difference 4 5) sourceC837) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA837 + difference 5 4) (sourceB837 + difference 4 5) sourceC837) = raw13834 := by
      apply Matrix.ext; unfold tripleCharges sourceA837 sourceB837 sourceC837 difference raw13834; decide +kernel
    rw [ha]
    exact (canonical13834 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA837 sourceB837 sourceC837
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm837, Integer.Sparse.eval]
  linarith only [hs]

def sourceA838 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceB838 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC838 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm838 : Integer.Sparse Master := [(Sum.inr 4802, 2), (Sum.inr 4805, 1), (Sum.inr 4833, 1), (Sum.inr 4893, 1), (Sum.inr 5226, 2), (Sum.inr 5227, 1), (Sum.inr 5231, 1), (Sum.inr 5255, 2), (Sum.inr 5256, 3), (Sum.inr 5257, 4), (Sum.inr 5263, 1), (Sum.inr 5265, 3), (Sum.inr 5271, 2), (Sum.inr 5273, 1), (Sum.inr 5290, 1), (Sum.inr 5292, 3), (Sum.inr 5307, 1)]

theorem sourceEq838 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm838 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA838 + difference 0 1) (sourceB838 + difference 1 0) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA838 + difference 0 1) (sourceB838 + difference 1 0) sourceC838) = raw13835 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13835; decide +kernel
    rw [ha]
    exact (canonical13835 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA838 + difference 0 2) (sourceB838 + difference 2 0) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA838 + difference 0 2) (sourceB838 + difference 2 0) sourceC838) = raw13836 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13836; decide +kernel
    rw [ha]
    exact (canonical13836 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA838 + difference 0 3) (sourceB838 + difference 3 0) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA838 + difference 0 3) (sourceB838 + difference 3 0) sourceC838) = raw13837 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13837; decide +kernel
    rw [ha]
    exact (canonical13837 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA838 + difference 0 4) (sourceB838 + difference 4 0) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA838 + difference 0 4) (sourceB838 + difference 4 0) sourceC838) = raw13838 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13838; decide +kernel
    rw [ha]
    exact (canonical13838 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA838 + difference 0 5) (sourceB838 + difference 5 0) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA838 + difference 0 5) (sourceB838 + difference 5 0) sourceC838) = raw13618 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13618; decide +kernel
    rw [ha]
    exact (canonical13618 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA838 + difference 1 0) (sourceB838 + difference 0 1) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA838 + difference 1 0) (sourceB838 + difference 0 1) sourceC838) = raw13839 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13839; decide +kernel
    rw [ha]
    exact (canonical13839 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA838 + difference 1 2) (sourceB838 + difference 2 1) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA838 + difference 1 2) (sourceB838 + difference 2 1) sourceC838) = raw13840 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13840; decide +kernel
    rw [ha]
    exact (canonical13840 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA838 + difference 1 3) (sourceB838 + difference 3 1) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA838 + difference 1 3) (sourceB838 + difference 3 1) sourceC838) = raw13841 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13841; decide +kernel
    rw [ha]
    exact (canonical13841 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA838 + difference 1 4) (sourceB838 + difference 4 1) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA838 + difference 1 4) (sourceB838 + difference 4 1) sourceC838) = raw13842 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13842; decide +kernel
    rw [ha]
    exact (canonical13842 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA838 + difference 1 5) (sourceB838 + difference 5 1) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA838 + difference 1 5) (sourceB838 + difference 5 1) sourceC838) = raw13623 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13623; decide +kernel
    rw [ha]
    exact (canonical13623 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA838 + difference 2 0) (sourceB838 + difference 0 2) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA838 + difference 2 0) (sourceB838 + difference 0 2) sourceC838) = raw13640 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13640; decide +kernel
    rw [ha]
    exact (canonical13640 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA838 + difference 2 1) (sourceB838 + difference 1 2) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA838 + difference 2 1) (sourceB838 + difference 1 2) sourceC838) = raw13641 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13641; decide +kernel
    rw [ha]
    exact (canonical13641 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA838 + difference 2 3) (sourceB838 + difference 3 2) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA838 + difference 2 3) (sourceB838 + difference 3 2) sourceC838) = raw13447 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13447; decide +kernel
    rw [ha]
    exact (canonical13447 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA838 + difference 2 4) (sourceB838 + difference 4 2) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA838 + difference 2 4) (sourceB838 + difference 4 2) sourceC838) = raw13443 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13443; decide +kernel
    rw [ha]
    exact (canonical13443 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA838 + difference 2 5) (sourceB838 + difference 5 2) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA838 + difference 2 5) (sourceB838 + difference 5 2) sourceC838) = raw13843 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13843; decide +kernel
    rw [ha]
    exact (canonical13843 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA838 + difference 3 0) (sourceB838 + difference 0 3) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA838 + difference 3 0) (sourceB838 + difference 0 3) sourceC838) = raw13844 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13844; decide +kernel
    rw [ha]
    exact (canonical13844 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA838 + difference 3 1) (sourceB838 + difference 1 3) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA838 + difference 3 1) (sourceB838 + difference 1 3) sourceC838) = raw13845 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13845; decide +kernel
    rw [ha]
    exact (canonical13845 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA838 + difference 3 2) (sourceB838 + difference 2 3) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA838 + difference 3 2) (sourceB838 + difference 2 3) sourceC838) = raw13846 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13846; decide +kernel
    rw [ha]
    exact (canonical13846 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA838 + difference 3 4) (sourceB838 + difference 4 3) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA838 + difference 3 4) (sourceB838 + difference 4 3) sourceC838) = raw13847 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13847; decide +kernel
    rw [ha]
    exact (canonical13847 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA838 + difference 3 5) (sourceB838 + difference 5 3) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA838 + difference 3 5) (sourceB838 + difference 5 3) sourceC838) = raw13632 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13632; decide +kernel
    rw [ha]
    exact (canonical13632 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA838 + difference 4 0) (sourceB838 + difference 0 4) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA838 + difference 4 0) (sourceB838 + difference 0 4) sourceC838) = raw13848 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13848; decide +kernel
    rw [ha]
    exact (canonical13848 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA838 + difference 4 1) (sourceB838 + difference 1 4) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA838 + difference 4 1) (sourceB838 + difference 1 4) sourceC838) = raw13849 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13849; decide +kernel
    rw [ha]
    exact (canonical13849 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA838 + difference 4 2) (sourceB838 + difference 2 4) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA838 + difference 4 2) (sourceB838 + difference 2 4) sourceC838) = raw13850 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13850; decide +kernel
    rw [ha]
    exact (canonical13850 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA838 + difference 4 3) (sourceB838 + difference 3 4) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA838 + difference 4 3) (sourceB838 + difference 3 4) sourceC838) = raw13851 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13851; decide +kernel
    rw [ha]
    exact (canonical13851 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA838 + difference 4 5) (sourceB838 + difference 5 4) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA838 + difference 4 5) (sourceB838 + difference 5 4) sourceC838) = raw13637 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13637; decide +kernel
    rw [ha]
    exact (canonical13637 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA838 + difference 5 0) (sourceB838 + difference 0 5) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA838 + difference 5 0) (sourceB838 + difference 0 5) sourceC838) = raw13852 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13852; decide +kernel
    rw [ha]
    exact (canonical13852 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA838 + difference 5 1) (sourceB838 + difference 1 5) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA838 + difference 5 1) (sourceB838 + difference 1 5) sourceC838) = raw13853 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13853; decide +kernel
    rw [ha]
    exact (canonical13853 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA838 + difference 5 2) (sourceB838 + difference 2 5) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA838 + difference 5 2) (sourceB838 + difference 2 5) sourceC838) = raw13854 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13854; decide +kernel
    rw [ha]
    exact (canonical13854 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA838 + difference 5 3) (sourceB838 + difference 3 5) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA838 + difference 5 3) (sourceB838 + difference 3 5) sourceC838) = raw13855 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13855; decide +kernel
    rw [ha]
    exact (canonical13855 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA838 + difference 5 4) (sourceB838 + difference 4 5) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA838 + difference 5 4) (sourceB838 + difference 4 5) sourceC838) = raw13856 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13856; decide +kernel
    rw [ha]
    exact (canonical13856 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA838 sourceB838 sourceC838
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm838, Integer.Sparse.eval]
  linarith only [hs]

def sourceA839 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceB839 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC839 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm839 : Integer.Sparse Master := [(Sum.inr 2202, 2), (Sum.inr 2204, 1), (Sum.inr 2214, 1), (Sum.inr 2263, 1), (Sum.inr 2669, 2), (Sum.inr 2671, 1), (Sum.inr 2676, 1), (Sum.inr 2718, 2), (Sum.inr 2720, 2), (Sum.inr 2721, 2), (Sum.inr 2728, 1), (Sum.inr 2730, 2), (Sum.inr 2739, 2), (Sum.inr 2741, 1), (Sum.inr 2764, 1), (Sum.inr 2766, 2), (Sum.inr 2785, 1), (Sum.inr 3037, 1), (Sum.inr 3085, 1), (Sum.inr 3087, 2), (Sum.inr 3100, 1)]

theorem sourceEq839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm839 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA839 + difference 0 1) (sourceB839 + difference 1 0) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA839 + difference 0 1) (sourceB839 + difference 1 0) sourceC839) = raw13857 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13857; decide +kernel
    rw [ha]
    exact (canonical13857 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA839 + difference 0 2) (sourceB839 + difference 2 0) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA839 + difference 0 2) (sourceB839 + difference 2 0) sourceC839) = raw13858 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13858; decide +kernel
    rw [ha]
    exact (canonical13858 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA839 + difference 0 3) (sourceB839 + difference 3 0) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA839 + difference 0 3) (sourceB839 + difference 3 0) sourceC839) = raw13859 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13859; decide +kernel
    rw [ha]
    exact (canonical13859 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA839 + difference 0 4) (sourceB839 + difference 4 0) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA839 + difference 0 4) (sourceB839 + difference 4 0) sourceC839) = raw13860 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13860; decide +kernel
    rw [ha]
    exact (canonical13860 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA839 + difference 0 5) (sourceB839 + difference 5 0) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA839 + difference 0 5) (sourceB839 + difference 5 0) sourceC839) = raw13644 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13644; decide +kernel
    rw [ha]
    exact (canonical13644 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA839 + difference 1 0) (sourceB839 + difference 0 1) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA839 + difference 1 0) (sourceB839 + difference 0 1) sourceC839) = raw13861 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13861; decide +kernel
    rw [ha]
    exact (canonical13861 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA839 + difference 1 2) (sourceB839 + difference 2 1) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA839 + difference 1 2) (sourceB839 + difference 2 1) sourceC839) = raw13862 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13862; decide +kernel
    rw [ha]
    exact (canonical13862 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA839 + difference 1 3) (sourceB839 + difference 3 1) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA839 + difference 1 3) (sourceB839 + difference 3 1) sourceC839) = raw13863 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13863; decide +kernel
    rw [ha]
    exact (canonical13863 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA839 + difference 1 4) (sourceB839 + difference 4 1) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA839 + difference 1 4) (sourceB839 + difference 4 1) sourceC839) = raw13864 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13864; decide +kernel
    rw [ha]
    exact (canonical13864 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA839 + difference 1 5) (sourceB839 + difference 5 1) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA839 + difference 1 5) (sourceB839 + difference 5 1) sourceC839) = raw13649 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13649; decide +kernel
    rw [ha]
    exact (canonical13649 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA839 + difference 2 0) (sourceB839 + difference 0 2) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA839 + difference 2 0) (sourceB839 + difference 0 2) sourceC839) = raw13668 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13668; decide +kernel
    rw [ha]
    exact (canonical13668 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA839 + difference 2 1) (sourceB839 + difference 1 2) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2785) := by
    have ha : (tripleCharges (sourceA839 + difference 2 1) (sourceB839 + difference 1 2) sourceC839) = raw13669 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13669; decide +kernel
    rw [ha]
    exact (canonical13669 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA839 + difference 2 3) (sourceB839 + difference 3 2) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA839 + difference 2 3) (sourceB839 + difference 3 2) sourceC839) = raw13671 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13671; decide +kernel
    rw [ha]
    exact (canonical13671 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA839 + difference 2 4) (sourceB839 + difference 4 2) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA839 + difference 2 4) (sourceB839 + difference 4 2) sourceC839) = raw13672 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13672; decide +kernel
    rw [ha]
    exact (canonical13672 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA839 + difference 2 5) (sourceB839 + difference 5 2) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA839 + difference 2 5) (sourceB839 + difference 5 2) sourceC839) = raw13865 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13865; decide +kernel
    rw [ha]
    exact (canonical13865 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA839 + difference 3 0) (sourceB839 + difference 0 3) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA839 + difference 3 0) (sourceB839 + difference 0 3) sourceC839) = raw13866 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13866; decide +kernel
    rw [ha]
    exact (canonical13866 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA839 + difference 3 1) (sourceB839 + difference 1 3) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA839 + difference 3 1) (sourceB839 + difference 1 3) sourceC839) = raw13867 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13867; decide +kernel
    rw [ha]
    exact (canonical13867 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA839 + difference 3 2) (sourceB839 + difference 2 3) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA839 + difference 3 2) (sourceB839 + difference 2 3) sourceC839) = raw13868 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13868; decide +kernel
    rw [ha]
    exact (canonical13868 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA839 + difference 3 4) (sourceB839 + difference 4 3) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA839 + difference 3 4) (sourceB839 + difference 4 3) sourceC839) = raw13869 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13869; decide +kernel
    rw [ha]
    exact (canonical13869 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA839 + difference 3 5) (sourceB839 + difference 5 3) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA839 + difference 3 5) (sourceB839 + difference 5 3) sourceC839) = raw13660 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13660; decide +kernel
    rw [ha]
    exact (canonical13660 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA839 + difference 4 0) (sourceB839 + difference 0 4) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA839 + difference 4 0) (sourceB839 + difference 0 4) sourceC839) = raw13870 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13870; decide +kernel
    rw [ha]
    exact (canonical13870 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA839 + difference 4 1) (sourceB839 + difference 1 4) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA839 + difference 4 1) (sourceB839 + difference 1 4) sourceC839) = raw13871 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13871; decide +kernel
    rw [ha]
    exact (canonical13871 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA839 + difference 4 2) (sourceB839 + difference 2 4) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA839 + difference 4 2) (sourceB839 + difference 2 4) sourceC839) = raw13872 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13872; decide +kernel
    rw [ha]
    exact (canonical13872 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA839 + difference 4 3) (sourceB839 + difference 3 4) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA839 + difference 4 3) (sourceB839 + difference 3 4) sourceC839) = raw13873 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13873; decide +kernel
    rw [ha]
    exact (canonical13873 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA839 + difference 4 5) (sourceB839 + difference 5 4) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA839 + difference 4 5) (sourceB839 + difference 5 4) sourceC839) = raw13665 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13665; decide +kernel
    rw [ha]
    exact (canonical13665 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA839 + difference 5 0) (sourceB839 + difference 0 5) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA839 + difference 5 0) (sourceB839 + difference 0 5) sourceC839) = raw13874 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13874; decide +kernel
    rw [ha]
    exact (canonical13874 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA839 + difference 5 1) (sourceB839 + difference 1 5) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA839 + difference 5 1) (sourceB839 + difference 1 5) sourceC839) = raw13875 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13875; decide +kernel
    rw [ha]
    exact (canonical13875 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA839 + difference 5 2) (sourceB839 + difference 2 5) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA839 + difference 5 2) (sourceB839 + difference 2 5) sourceC839) = raw13876 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13876; decide +kernel
    rw [ha]
    exact (canonical13876 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA839 + difference 5 3) (sourceB839 + difference 3 5) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA839 + difference 5 3) (sourceB839 + difference 3 5) sourceC839) = raw13877 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13877; decide +kernel
    rw [ha]
    exact (canonical13877 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA839 + difference 5 4) (sourceB839 + difference 4 5) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA839 + difference 5 4) (sourceB839 + difference 4 5) sourceC839) = raw13878 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13878; decide +kernel
    rw [ha]
    exact (canonical13878 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA839 sourceB839 sourceC839
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm839, Integer.Sparse.eval]
  linarith only [hs]

def sourceA840 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB840 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC840 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceForm840 : Integer.Sparse Master := [(Sum.inr 4616, 2), (Sum.inr 4617, 1), (Sum.inr 4619, 1), (Sum.inr 4620, 1), (Sum.inr 5160, 2), (Sum.inr 5163, 2), (Sum.inr 5164, 2), (Sum.inr 5173, 2), (Sum.inr 5271, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5276, 1), (Sum.inr 5289, 2), (Sum.inr 5291, 1), (Sum.inr 5295, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 1), (Sum.inr 5438, 2), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5451, 1)]

theorem sourceEq840 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm840 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA840 + difference 0 1) (sourceB840 + difference 1 0) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA840 + difference 0 1) (sourceB840 + difference 1 0) sourceC840) = raw13879 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13879; decide +kernel
    rw [ha]
    exact (canonical13879 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA840 + difference 0 2) (sourceB840 + difference 2 0) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA840 + difference 0 2) (sourceB840 + difference 2 0) sourceC840) = raw13880 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13880; decide +kernel
    rw [ha]
    exact (canonical13880 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA840 + difference 0 3) (sourceB840 + difference 3 0) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA840 + difference 0 3) (sourceB840 + difference 3 0) sourceC840) = raw13881 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13881; decide +kernel
    rw [ha]
    exact (canonical13881 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA840 + difference 0 4) (sourceB840 + difference 4 0) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA840 + difference 0 4) (sourceB840 + difference 4 0) sourceC840) = raw13882 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13882; decide +kernel
    rw [ha]
    exact (canonical13882 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA840 + difference 0 5) (sourceB840 + difference 5 0) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA840 + difference 0 5) (sourceB840 + difference 5 0) sourceC840) = raw13883 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13883; decide +kernel
    rw [ha]
    exact (canonical13883 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA840 + difference 1 0) (sourceB840 + difference 0 1) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA840 + difference 1 0) (sourceB840 + difference 0 1) sourceC840) = raw13884 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13884; decide +kernel
    rw [ha]
    exact (canonical13884 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA840 + difference 1 2) (sourceB840 + difference 2 1) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA840 + difference 1 2) (sourceB840 + difference 2 1) sourceC840) = raw13885 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13885; decide +kernel
    rw [ha]
    exact (canonical13885 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA840 + difference 1 3) (sourceB840 + difference 3 1) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA840 + difference 1 3) (sourceB840 + difference 3 1) sourceC840) = raw13886 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13886; decide +kernel
    rw [ha]
    exact (canonical13886 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA840 + difference 1 4) (sourceB840 + difference 4 1) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA840 + difference 1 4) (sourceB840 + difference 4 1) sourceC840) = raw13887 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13887; decide +kernel
    rw [ha]
    exact (canonical13887 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA840 + difference 1 5) (sourceB840 + difference 5 1) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA840 + difference 1 5) (sourceB840 + difference 5 1) sourceC840) = raw13888 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13888; decide +kernel
    rw [ha]
    exact (canonical13888 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA840 + difference 2 0) (sourceB840 + difference 0 2) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA840 + difference 2 0) (sourceB840 + difference 0 2) sourceC840) = raw13889 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13889; decide +kernel
    rw [ha]
    exact (canonical13889 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA840 + difference 2 1) (sourceB840 + difference 1 2) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA840 + difference 2 1) (sourceB840 + difference 1 2) sourceC840) = raw13890 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13890; decide +kernel
    rw [ha]
    exact (canonical13890 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA840 + difference 2 3) (sourceB840 + difference 3 2) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA840 + difference 2 3) (sourceB840 + difference 3 2) sourceC840) = raw13891 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13891; decide +kernel
    rw [ha]
    exact (canonical13891 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA840 + difference 2 4) (sourceB840 + difference 4 2) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA840 + difference 2 4) (sourceB840 + difference 4 2) sourceC840) = raw13892 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13892; decide +kernel
    rw [ha]
    exact (canonical13892 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA840 + difference 2 5) (sourceB840 + difference 5 2) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA840 + difference 2 5) (sourceB840 + difference 5 2) sourceC840) = raw13893 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13893; decide +kernel
    rw [ha]
    exact (canonical13893 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA840 + difference 3 0) (sourceB840 + difference 0 3) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA840 + difference 3 0) (sourceB840 + difference 0 3) sourceC840) = raw13894 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13894; decide +kernel
    rw [ha]
    exact (canonical13894 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA840 + difference 3 1) (sourceB840 + difference 1 3) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA840 + difference 3 1) (sourceB840 + difference 1 3) sourceC840) = raw13895 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13895; decide +kernel
    rw [ha]
    exact (canonical13895 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA840 + difference 3 2) (sourceB840 + difference 2 3) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA840 + difference 3 2) (sourceB840 + difference 2 3) sourceC840) = raw13896 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13896; decide +kernel
    rw [ha]
    exact (canonical13896 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA840 + difference 3 4) (sourceB840 + difference 4 3) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA840 + difference 3 4) (sourceB840 + difference 4 3) sourceC840) = raw13897 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13897; decide +kernel
    rw [ha]
    exact (canonical13897 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA840 + difference 3 5) (sourceB840 + difference 5 3) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA840 + difference 3 5) (sourceB840 + difference 5 3) sourceC840) = raw13898 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13898; decide +kernel
    rw [ha]
    exact (canonical13898 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA840 + difference 4 0) (sourceB840 + difference 0 4) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4620) := by
    have ha : (tripleCharges (sourceA840 + difference 4 0) (sourceB840 + difference 0 4) sourceC840) = raw13899 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13899; decide +kernel
    rw [ha]
    exact (canonical13899 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA840 + difference 4 1) (sourceB840 + difference 1 4) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA840 + difference 4 1) (sourceB840 + difference 1 4) sourceC840) = raw13900 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13900; decide +kernel
    rw [ha]
    exact (canonical13900 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA840 + difference 4 2) (sourceB840 + difference 2 4) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA840 + difference 4 2) (sourceB840 + difference 2 4) sourceC840) = raw13901 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13901; decide +kernel
    rw [ha]
    exact (canonical13901 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA840 + difference 4 3) (sourceB840 + difference 3 4) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA840 + difference 4 3) (sourceB840 + difference 3 4) sourceC840) = raw13902 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13902; decide +kernel
    rw [ha]
    exact (canonical13902 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA840 + difference 4 5) (sourceB840 + difference 5 4) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA840 + difference 4 5) (sourceB840 + difference 5 4) sourceC840) = raw13903 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13903; decide +kernel
    rw [ha]
    exact (canonical13903 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA840 + difference 5 0) (sourceB840 + difference 0 5) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA840 + difference 5 0) (sourceB840 + difference 0 5) sourceC840) = raw13904 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13904; decide +kernel
    rw [ha]
    exact (canonical13904 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA840 + difference 5 1) (sourceB840 + difference 1 5) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA840 + difference 5 1) (sourceB840 + difference 1 5) sourceC840) = raw13905 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13905; decide +kernel
    rw [ha]
    exact (canonical13905 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA840 + difference 5 2) (sourceB840 + difference 2 5) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA840 + difference 5 2) (sourceB840 + difference 2 5) sourceC840) = raw13906 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13906; decide +kernel
    rw [ha]
    exact (canonical13906 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA840 + difference 5 3) (sourceB840 + difference 3 5) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA840 + difference 5 3) (sourceB840 + difference 3 5) sourceC840) = raw13907 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13907; decide +kernel
    rw [ha]
    exact (canonical13907 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA840 + difference 5 4) (sourceB840 + difference 4 5) sourceC840) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA840 + difference 5 4) (sourceB840 + difference 4 5) sourceC840) = raw13908 := by
      apply Matrix.ext; unfold tripleCharges sourceA840 sourceB840 sourceC840 difference raw13908; decide +kernel
    rw [ha]
    exact (canonical13908 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA840 sourceB840 sourceC840
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm840, Integer.Sparse.eval]
  linarith only [hs]

def sourceA841 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB841 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC841 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceForm841 : Integer.Sparse Master := [(Sum.inr 1291, 2), (Sum.inr 1292, 1), (Sum.inr 1295, 1), (Sum.inr 1302, 1), (Sum.inr 2951, 2), (Sum.inr 2952, 2), (Sum.inr 2955, 2), (Sum.inr 2961, 2), (Sum.inr 3051, 2), (Sum.inr 3052, 1), (Sum.inr 3055, 1), (Sum.inr 3097, 2), (Sum.inr 3098, 1), (Sum.inr 3103, 1), (Sum.inr 3109, 2), (Sum.inr 3110, 1), (Sum.inr 3112, 1), (Sum.inr 3862, 1), (Sum.inr 3987, 1), (Sum.inr 3993, 2), (Sum.inr 4001, 1)]

theorem sourceEq841 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm841 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA841 + difference 0 1) (sourceB841 + difference 1 0) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA841 + difference 0 1) (sourceB841 + difference 1 0) sourceC841) = raw13909 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13909; decide +kernel
    rw [ha]
    exact (canonical13909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA841 + difference 0 2) (sourceB841 + difference 2 0) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA841 + difference 0 2) (sourceB841 + difference 2 0) sourceC841) = raw13910 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13910; decide +kernel
    rw [ha]
    exact (canonical13910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA841 + difference 0 3) (sourceB841 + difference 3 0) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA841 + difference 0 3) (sourceB841 + difference 3 0) sourceC841) = raw13911 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13911; decide +kernel
    rw [ha]
    exact (canonical13911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA841 + difference 0 4) (sourceB841 + difference 4 0) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA841 + difference 0 4) (sourceB841 + difference 4 0) sourceC841) = raw13912 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13912; decide +kernel
    rw [ha]
    exact (canonical13912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA841 + difference 0 5) (sourceB841 + difference 5 0) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA841 + difference 0 5) (sourceB841 + difference 5 0) sourceC841) = raw13913 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13913; decide +kernel
    rw [ha]
    exact (canonical13913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA841 + difference 1 0) (sourceB841 + difference 0 1) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA841 + difference 1 0) (sourceB841 + difference 0 1) sourceC841) = raw13914 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13914; decide +kernel
    rw [ha]
    exact (canonical13914 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA841 + difference 1 2) (sourceB841 + difference 2 1) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA841 + difference 1 2) (sourceB841 + difference 2 1) sourceC841) = raw13915 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13915; decide +kernel
    rw [ha]
    exact (canonical13915 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA841 + difference 1 3) (sourceB841 + difference 3 1) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA841 + difference 1 3) (sourceB841 + difference 3 1) sourceC841) = raw13916 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13916; decide +kernel
    rw [ha]
    exact (canonical13916 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA841 + difference 1 4) (sourceB841 + difference 4 1) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA841 + difference 1 4) (sourceB841 + difference 4 1) sourceC841) = raw13917 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13917; decide +kernel
    rw [ha]
    exact (canonical13917 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA841 + difference 1 5) (sourceB841 + difference 5 1) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA841 + difference 1 5) (sourceB841 + difference 5 1) sourceC841) = raw13918 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13918; decide +kernel
    rw [ha]
    exact (canonical13918 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA841 + difference 2 0) (sourceB841 + difference 0 2) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA841 + difference 2 0) (sourceB841 + difference 0 2) sourceC841) = raw13919 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13919; decide +kernel
    rw [ha]
    exact (canonical13919 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA841 + difference 2 1) (sourceB841 + difference 1 2) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA841 + difference 2 1) (sourceB841 + difference 1 2) sourceC841) = raw13920 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13920; decide +kernel
    rw [ha]
    exact (canonical13920 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA841 + difference 2 3) (sourceB841 + difference 3 2) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA841 + difference 2 3) (sourceB841 + difference 3 2) sourceC841) = raw13921 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13921; decide +kernel
    rw [ha]
    exact (canonical13921 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA841 + difference 2 4) (sourceB841 + difference 4 2) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA841 + difference 2 4) (sourceB841 + difference 4 2) sourceC841) = raw13922 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13922; decide +kernel
    rw [ha]
    exact (canonical13922 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA841 + difference 2 5) (sourceB841 + difference 5 2) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA841 + difference 2 5) (sourceB841 + difference 5 2) sourceC841) = raw13923 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13923; decide +kernel
    rw [ha]
    exact (canonical13923 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA841 + difference 3 0) (sourceB841 + difference 0 3) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1302) := by
    have ha : (tripleCharges (sourceA841 + difference 3 0) (sourceB841 + difference 0 3) sourceC841) = raw13924 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13924; decide +kernel
    rw [ha]
    exact (canonical13924 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA841 + difference 3 1) (sourceB841 + difference 1 3) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2961) := by
    have ha : (tripleCharges (sourceA841 + difference 3 1) (sourceB841 + difference 1 3) sourceC841) = raw13925 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13925; decide +kernel
    rw [ha]
    exact (canonical13925 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA841 + difference 3 2) (sourceB841 + difference 2 3) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2961) := by
    have ha : (tripleCharges (sourceA841 + difference 3 2) (sourceB841 + difference 2 3) sourceC841) = raw13926 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13926; decide +kernel
    rw [ha]
    exact (canonical13926 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA841 + difference 3 4) (sourceB841 + difference 4 3) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA841 + difference 3 4) (sourceB841 + difference 4 3) sourceC841) = raw13927 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13927; decide +kernel
    rw [ha]
    exact (canonical13927 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA841 + difference 3 5) (sourceB841 + difference 5 3) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA841 + difference 3 5) (sourceB841 + difference 5 3) sourceC841) = raw13928 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13928; decide +kernel
    rw [ha]
    exact (canonical13928 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA841 + difference 4 0) (sourceB841 + difference 0 4) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1295) := by
    have ha : (tripleCharges (sourceA841 + difference 4 0) (sourceB841 + difference 0 4) sourceC841) = raw13929 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13929; decide +kernel
    rw [ha]
    exact (canonical13929 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA841 + difference 4 1) (sourceB841 + difference 1 4) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA841 + difference 4 1) (sourceB841 + difference 1 4) sourceC841) = raw13930 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13930; decide +kernel
    rw [ha]
    exact (canonical13930 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA841 + difference 4 2) (sourceB841 + difference 2 4) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA841 + difference 4 2) (sourceB841 + difference 2 4) sourceC841) = raw13931 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13931; decide +kernel
    rw [ha]
    exact (canonical13931 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA841 + difference 4 3) (sourceB841 + difference 3 4) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA841 + difference 4 3) (sourceB841 + difference 3 4) sourceC841) = raw13932 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13932; decide +kernel
    rw [ha]
    exact (canonical13932 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA841 + difference 4 5) (sourceB841 + difference 5 4) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA841 + difference 4 5) (sourceB841 + difference 5 4) sourceC841) = raw13933 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13933; decide +kernel
    rw [ha]
    exact (canonical13933 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA841 + difference 5 0) (sourceB841 + difference 0 5) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1292) := by
    have ha : (tripleCharges (sourceA841 + difference 5 0) (sourceB841 + difference 0 5) sourceC841) = raw13934 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13934; decide +kernel
    rw [ha]
    exact (canonical13934 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA841 + difference 5 1) (sourceB841 + difference 1 5) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA841 + difference 5 1) (sourceB841 + difference 1 5) sourceC841) = raw13935 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13935; decide +kernel
    rw [ha]
    exact (canonical13935 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA841 + difference 5 2) (sourceB841 + difference 2 5) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA841 + difference 5 2) (sourceB841 + difference 2 5) sourceC841) = raw13936 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13936; decide +kernel
    rw [ha]
    exact (canonical13936 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA841 + difference 5 3) (sourceB841 + difference 3 5) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA841 + difference 5 3) (sourceB841 + difference 3 5) sourceC841) = raw13937 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13937; decide +kernel
    rw [ha]
    exact (canonical13937 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA841 + difference 5 4) (sourceB841 + difference 4 5) sourceC841) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA841 + difference 5 4) (sourceB841 + difference 4 5) sourceC841) = raw13938 := by
      apply Matrix.ext; unfold tripleCharges sourceA841 sourceB841 sourceC841 difference raw13938; decide +kernel
    rw [ha]
    exact (canonical13938 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA841 sourceB841 sourceC841
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm841, Integer.Sparse.eval]
  linarith only [hs]

def sourceA842 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB842 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC842 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceForm842 : Integer.Sparse Master := [(Sum.inr 2735, 2), (Sum.inr 2737, 1), (Sum.inr 2744, 1), (Sum.inr 2781, 1), (Sum.inr 3303, 2), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 3534, 2), (Sum.inr 3547, 1), (Sum.inr 3548, 1), (Sum.inr 3558, 2), (Sum.inr 3564, 2), (Sum.inr 3565, 2), (Sum.inr 3572, 2), (Sum.inr 3573, 2), (Sum.inr 3582, 1), (Sum.inr 3584, 1), (Sum.inr 3861, 1), (Sum.inr 3876, 2), (Sum.inr 3888, 1), (Sum.inr 3889, 1)]

theorem sourceEq842 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm842 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA842 + difference 0 1) (sourceB842 + difference 1 0) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA842 + difference 0 1) (sourceB842 + difference 1 0) sourceC842) = raw13939 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13939; decide +kernel
    rw [ha]
    exact (canonical13939 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA842 + difference 0 2) (sourceB842 + difference 2 0) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA842 + difference 0 2) (sourceB842 + difference 2 0) sourceC842) = raw13940 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13940; decide +kernel
    rw [ha]
    exact (canonical13940 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA842 + difference 0 3) (sourceB842 + difference 3 0) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA842 + difference 0 3) (sourceB842 + difference 3 0) sourceC842) = raw13941 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13941; decide +kernel
    rw [ha]
    exact (canonical13941 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA842 + difference 0 4) (sourceB842 + difference 4 0) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA842 + difference 0 4) (sourceB842 + difference 4 0) sourceC842) = raw13942 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13942; decide +kernel
    rw [ha]
    exact (canonical13942 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA842 + difference 0 5) (sourceB842 + difference 5 0) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3861) := by
    have ha : (tripleCharges (sourceA842 + difference 0 5) (sourceB842 + difference 5 0) sourceC842) = raw13943 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13943; decide +kernel
    rw [ha]
    exact (canonical13943 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA842 + difference 1 0) (sourceB842 + difference 0 1) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA842 + difference 1 0) (sourceB842 + difference 0 1) sourceC842) = raw13944 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13944; decide +kernel
    rw [ha]
    exact (canonical13944 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA842 + difference 1 2) (sourceB842 + difference 2 1) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA842 + difference 1 2) (sourceB842 + difference 2 1) sourceC842) = raw13945 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13945; decide +kernel
    rw [ha]
    exact (canonical13945 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA842 + difference 1 3) (sourceB842 + difference 3 1) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA842 + difference 1 3) (sourceB842 + difference 3 1) sourceC842) = raw13946 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13946; decide +kernel
    rw [ha]
    exact (canonical13946 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA842 + difference 1 4) (sourceB842 + difference 4 1) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA842 + difference 1 4) (sourceB842 + difference 4 1) sourceC842) = raw13947 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13947; decide +kernel
    rw [ha]
    exact (canonical13947 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA842 + difference 1 5) (sourceB842 + difference 5 1) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA842 + difference 1 5) (sourceB842 + difference 5 1) sourceC842) = raw13948 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13948; decide +kernel
    rw [ha]
    exact (canonical13948 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA842 + difference 2 0) (sourceB842 + difference 0 2) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA842 + difference 2 0) (sourceB842 + difference 0 2) sourceC842) = raw13949 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13949; decide +kernel
    rw [ha]
    exact (canonical13949 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA842 + difference 2 1) (sourceB842 + difference 1 2) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA842 + difference 2 1) (sourceB842 + difference 1 2) sourceC842) = raw13950 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13950; decide +kernel
    rw [ha]
    exact (canonical13950 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA842 + difference 2 3) (sourceB842 + difference 3 2) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA842 + difference 2 3) (sourceB842 + difference 3 2) sourceC842) = raw13951 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13951; decide +kernel
    rw [ha]
    exact (canonical13951 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA842 + difference 2 4) (sourceB842 + difference 4 2) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA842 + difference 2 4) (sourceB842 + difference 4 2) sourceC842) = raw13952 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13952; decide +kernel
    rw [ha]
    exact (canonical13952 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA842 + difference 2 5) (sourceB842 + difference 5 2) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA842 + difference 2 5) (sourceB842 + difference 5 2) sourceC842) = raw13953 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13953; decide +kernel
    rw [ha]
    exact (canonical13953 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA842 + difference 3 0) (sourceB842 + difference 0 3) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA842 + difference 3 0) (sourceB842 + difference 0 3) sourceC842) = raw13954 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13954; decide +kernel
    rw [ha]
    exact (canonical13954 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA842 + difference 3 1) (sourceB842 + difference 1 3) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA842 + difference 3 1) (sourceB842 + difference 1 3) sourceC842) = raw13955 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13955; decide +kernel
    rw [ha]
    exact (canonical13955 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA842 + difference 3 2) (sourceB842 + difference 2 3) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA842 + difference 3 2) (sourceB842 + difference 2 3) sourceC842) = raw13956 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13956; decide +kernel
    rw [ha]
    exact (canonical13956 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA842 + difference 3 4) (sourceB842 + difference 4 3) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA842 + difference 3 4) (sourceB842 + difference 4 3) sourceC842) = raw13957 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13957; decide +kernel
    rw [ha]
    exact (canonical13957 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA842 + difference 3 5) (sourceB842 + difference 5 3) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA842 + difference 3 5) (sourceB842 + difference 5 3) sourceC842) = raw13958 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13958; decide +kernel
    rw [ha]
    exact (canonical13958 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA842 + difference 4 0) (sourceB842 + difference 0 4) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA842 + difference 4 0) (sourceB842 + difference 0 4) sourceC842) = raw13959 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13959; decide +kernel
    rw [ha]
    exact (canonical13959 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA842 + difference 4 1) (sourceB842 + difference 1 4) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA842 + difference 4 1) (sourceB842 + difference 1 4) sourceC842) = raw13960 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13960; decide +kernel
    rw [ha]
    exact (canonical13960 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA842 + difference 4 2) (sourceB842 + difference 2 4) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA842 + difference 4 2) (sourceB842 + difference 2 4) sourceC842) = raw13961 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13961; decide +kernel
    rw [ha]
    exact (canonical13961 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA842 + difference 4 3) (sourceB842 + difference 3 4) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA842 + difference 4 3) (sourceB842 + difference 3 4) sourceC842) = raw13962 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13962; decide +kernel
    rw [ha]
    exact (canonical13962 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA842 + difference 4 5) (sourceB842 + difference 5 4) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA842 + difference 4 5) (sourceB842 + difference 5 4) sourceC842) = raw13963 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13963; decide +kernel
    rw [ha]
    exact (canonical13963 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA842 + difference 5 0) (sourceB842 + difference 0 5) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA842 + difference 5 0) (sourceB842 + difference 0 5) sourceC842) = raw13964 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13964; decide +kernel
    rw [ha]
    exact (canonical13964 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA842 + difference 5 1) (sourceB842 + difference 1 5) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA842 + difference 5 1) (sourceB842 + difference 1 5) sourceC842) = raw13965 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13965; decide +kernel
    rw [ha]
    exact (canonical13965 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA842 + difference 5 2) (sourceB842 + difference 2 5) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA842 + difference 5 2) (sourceB842 + difference 2 5) sourceC842) = raw13966 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13966; decide +kernel
    rw [ha]
    exact (canonical13966 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA842 + difference 5 3) (sourceB842 + difference 3 5) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA842 + difference 5 3) (sourceB842 + difference 3 5) sourceC842) = raw13967 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13967; decide +kernel
    rw [ha]
    exact (canonical13967 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA842 + difference 5 4) (sourceB842 + difference 4 5) sourceC842) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA842 + difference 5 4) (sourceB842 + difference 4 5) sourceC842) = raw13968 := by
      apply Matrix.ext; unfold tripleCharges sourceA842 sourceB842 sourceC842 difference raw13968; decide +kernel
    rw [ha]
    exact (canonical13968 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA842 sourceB842 sourceC842
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm842, Integer.Sparse.eval]
  linarith only [hs]

def sourceA843 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB843 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC843 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceForm843 : Integer.Sparse Master := [(Sum.inr 4489, 2), (Sum.inr 4490, 1), (Sum.inr 4491, 1), (Sum.inr 4503, 1), (Sum.inr 5093, 2), (Sum.inr 5094, 2), (Sum.inr 5095, 2), (Sum.inr 5105, 2), (Sum.inr 5110, 1), (Sum.inr 5237, 2), (Sum.inr 5238, 1), (Sum.inr 5290, 2), (Sum.inr 5291, 1), (Sum.inr 5294, 1), (Sum.inr 5304, 2), (Sum.inr 5305, 1), (Sum.inr 5310, 1), (Sum.inr 5451, 1), (Sum.inr 5484, 2), (Sum.inr 5492, 1), (Sum.inr 5494, 1)]

theorem sourceEq843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm843 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA843 + difference 0 1) (sourceB843 + difference 1 0) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA843 + difference 0 1) (sourceB843 + difference 1 0) sourceC843) = raw13969 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13969; decide +kernel
    rw [ha]
    exact (canonical13969 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA843 + difference 0 2) (sourceB843 + difference 2 0) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA843 + difference 0 2) (sourceB843 + difference 2 0) sourceC843) = raw13970 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13970; decide +kernel
    rw [ha]
    exact (canonical13970 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA843 + difference 0 3) (sourceB843 + difference 3 0) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA843 + difference 0 3) (sourceB843 + difference 3 0) sourceC843) = raw8006 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw8006; decide +kernel
    rw [ha]
    exact (canonical8006 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA843 + difference 0 4) (sourceB843 + difference 4 0) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5494) := by
    have ha : (tripleCharges (sourceA843 + difference 0 4) (sourceB843 + difference 4 0) sourceC843) = raw13971 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13971; decide +kernel
    rw [ha]
    exact (canonical13971 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA843 + difference 0 5) (sourceB843 + difference 5 0) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA843 + difference 0 5) (sourceB843 + difference 5 0) sourceC843) = raw13972 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13972; decide +kernel
    rw [ha]
    exact (canonical13972 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA843 + difference 1 0) (sourceB843 + difference 0 1) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA843 + difference 1 0) (sourceB843 + difference 0 1) sourceC843) = raw13973 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13973; decide +kernel
    rw [ha]
    exact (canonical13973 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA843 + difference 1 2) (sourceB843 + difference 2 1) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5093) := by
    have ha : (tripleCharges (sourceA843 + difference 1 2) (sourceB843 + difference 2 1) sourceC843) = raw13974 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13974; decide +kernel
    rw [ha]
    exact (canonical13974 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA843 + difference 1 3) (sourceB843 + difference 3 1) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA843 + difference 1 3) (sourceB843 + difference 3 1) sourceC843) = raw8011 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw8011; decide +kernel
    rw [ha]
    exact (canonical8011 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA843 + difference 1 4) (sourceB843 + difference 4 1) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA843 + difference 1 4) (sourceB843 + difference 4 1) sourceC843) = raw13975 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13975; decide +kernel
    rw [ha]
    exact (canonical13975 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA843 + difference 1 5) (sourceB843 + difference 5 1) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA843 + difference 1 5) (sourceB843 + difference 5 1) sourceC843) = raw13976 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13976; decide +kernel
    rw [ha]
    exact (canonical13976 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA843 + difference 2 0) (sourceB843 + difference 0 2) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA843 + difference 2 0) (sourceB843 + difference 0 2) sourceC843) = raw13977 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13977; decide +kernel
    rw [ha]
    exact (canonical13977 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA843 + difference 2 1) (sourceB843 + difference 1 2) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5093) := by
    have ha : (tripleCharges (sourceA843 + difference 2 1) (sourceB843 + difference 1 2) sourceC843) = raw13978 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13978; decide +kernel
    rw [ha]
    exact (canonical13978 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA843 + difference 2 3) (sourceB843 + difference 3 2) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA843 + difference 2 3) (sourceB843 + difference 3 2) sourceC843) = raw8016 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw8016; decide +kernel
    rw [ha]
    exact (canonical8016 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA843 + difference 2 4) (sourceB843 + difference 4 2) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA843 + difference 2 4) (sourceB843 + difference 4 2) sourceC843) = raw13979 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13979; decide +kernel
    rw [ha]
    exact (canonical13979 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA843 + difference 2 5) (sourceB843 + difference 5 2) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA843 + difference 2 5) (sourceB843 + difference 5 2) sourceC843) = raw13980 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13980; decide +kernel
    rw [ha]
    exact (canonical13980 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA843 + difference 3 0) (sourceB843 + difference 0 3) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA843 + difference 3 0) (sourceB843 + difference 0 3) sourceC843) = raw13981 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13981; decide +kernel
    rw [ha]
    exact (canonical13981 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA843 + difference 3 1) (sourceB843 + difference 1 3) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA843 + difference 3 1) (sourceB843 + difference 1 3) sourceC843) = raw13982 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13982; decide +kernel
    rw [ha]
    exact (canonical13982 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA843 + difference 3 2) (sourceB843 + difference 2 3) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA843 + difference 3 2) (sourceB843 + difference 2 3) sourceC843) = raw13983 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13983; decide +kernel
    rw [ha]
    exact (canonical13983 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA843 + difference 3 4) (sourceB843 + difference 4 3) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA843 + difference 3 4) (sourceB843 + difference 4 3) sourceC843) = raw13984 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13984; decide +kernel
    rw [ha]
    exact (canonical13984 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA843 + difference 3 5) (sourceB843 + difference 5 3) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA843 + difference 3 5) (sourceB843 + difference 5 3) sourceC843) = raw13985 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13985; decide +kernel
    rw [ha]
    exact (canonical13985 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA843 + difference 4 0) (sourceB843 + difference 0 4) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA843 + difference 4 0) (sourceB843 + difference 0 4) sourceC843) = raw13986 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13986; decide +kernel
    rw [ha]
    exact (canonical13986 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA843 + difference 4 1) (sourceB843 + difference 1 4) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA843 + difference 4 1) (sourceB843 + difference 1 4) sourceC843) = raw13987 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13987; decide +kernel
    rw [ha]
    exact (canonical13987 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA843 + difference 4 2) (sourceB843 + difference 2 4) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA843 + difference 4 2) (sourceB843 + difference 2 4) sourceC843) = raw13988 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13988; decide +kernel
    rw [ha]
    exact (canonical13988 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA843 + difference 4 3) (sourceB843 + difference 3 4) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA843 + difference 4 3) (sourceB843 + difference 3 4) sourceC843) = raw8026 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw8026; decide +kernel
    rw [ha]
    exact (canonical8026 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA843 + difference 4 5) (sourceB843 + difference 5 4) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA843 + difference 4 5) (sourceB843 + difference 5 4) sourceC843) = raw13989 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13989; decide +kernel
    rw [ha]
    exact (canonical13989 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA843 + difference 5 0) (sourceB843 + difference 0 5) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA843 + difference 5 0) (sourceB843 + difference 0 5) sourceC843) = raw8017 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw8017; decide +kernel
    rw [ha]
    exact (canonical8017 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA843 + difference 5 1) (sourceB843 + difference 1 5) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA843 + difference 5 1) (sourceB843 + difference 1 5) sourceC843) = raw8018 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw8018; decide +kernel
    rw [ha]
    exact (canonical8018 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA843 + difference 5 2) (sourceB843 + difference 2 5) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA843 + difference 5 2) (sourceB843 + difference 2 5) sourceC843) = raw8019 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw8019; decide +kernel
    rw [ha]
    exact (canonical8019 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA843 + difference 5 3) (sourceB843 + difference 3 5) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA843 + difference 5 3) (sourceB843 + difference 3 5) sourceC843) = raw13990 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw13990; decide +kernel
    rw [ha]
    exact (canonical13990 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA843 + difference 5 4) (sourceB843 + difference 4 5) sourceC843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA843 + difference 5 4) (sourceB843 + difference 4 5) sourceC843) = raw8020 := by
      apply Matrix.ext; unfold tripleCharges sourceA843 sourceB843 sourceC843 difference raw8020; decide +kernel
    rw [ha]
    exact (canonical8020 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA843 sourceB843 sourceC843
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm843, Integer.Sparse.eval]
  linarith only [hs]

def sourceA844 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB844 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC844 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceForm844 : Integer.Sparse Master := [(Sum.inr 1073, 2), (Sum.inr 1074, 1), (Sum.inr 1075, 1), (Sum.inr 1087, 1), (Sum.inr 2503, 2), (Sum.inr 2504, 2), (Sum.inr 2505, 2), (Sum.inr 2515, 2), (Sum.inr 2684, 2), (Sum.inr 2685, 1), (Sum.inr 2686, 1), (Sum.inr 2764, 2), (Sum.inr 2765, 1), (Sum.inr 2768, 1), (Sum.inr 2782, 2), (Sum.inr 2783, 1), (Sum.inr 2788, 1), (Sum.inr 3913, 1), (Sum.inr 3983, 2), (Sum.inr 4017, 1), (Sum.inr 4020, 1)]

theorem sourceEq844 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm844 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA844 + difference 0 1) (sourceB844 + difference 1 0) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA844 + difference 0 1) (sourceB844 + difference 1 0) sourceC844) = raw13991 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw13991; decide +kernel
    rw [ha]
    exact (canonical13991 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA844 + difference 0 2) (sourceB844 + difference 2 0) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA844 + difference 0 2) (sourceB844 + difference 2 0) sourceC844) = raw13992 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw13992; decide +kernel
    rw [ha]
    exact (canonical13992 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA844 + difference 0 3) (sourceB844 + difference 3 0) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA844 + difference 0 3) (sourceB844 + difference 3 0) sourceC844) = raw8036 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw8036; decide +kernel
    rw [ha]
    exact (canonical8036 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA844 + difference 0 4) (sourceB844 + difference 4 0) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4020) := by
    have ha : (tripleCharges (sourceA844 + difference 0 4) (sourceB844 + difference 4 0) sourceC844) = raw13993 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw13993; decide +kernel
    rw [ha]
    exact (canonical13993 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA844 + difference 0 5) (sourceB844 + difference 5 0) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA844 + difference 0 5) (sourceB844 + difference 5 0) sourceC844) = raw13994 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw13994; decide +kernel
    rw [ha]
    exact (canonical13994 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA844 + difference 1 0) (sourceB844 + difference 0 1) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA844 + difference 1 0) (sourceB844 + difference 0 1) sourceC844) = raw13995 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw13995; decide +kernel
    rw [ha]
    exact (canonical13995 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA844 + difference 1 2) (sourceB844 + difference 2 1) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2503) := by
    have ha : (tripleCharges (sourceA844 + difference 1 2) (sourceB844 + difference 2 1) sourceC844) = raw13996 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw13996; decide +kernel
    rw [ha]
    exact (canonical13996 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA844 + difference 1 3) (sourceB844 + difference 3 1) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA844 + difference 1 3) (sourceB844 + difference 3 1) sourceC844) = raw8041 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw8041; decide +kernel
    rw [ha]
    exact (canonical8041 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA844 + difference 1 4) (sourceB844 + difference 4 1) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA844 + difference 1 4) (sourceB844 + difference 4 1) sourceC844) = raw13997 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw13997; decide +kernel
    rw [ha]
    exact (canonical13997 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA844 + difference 1 5) (sourceB844 + difference 5 1) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA844 + difference 1 5) (sourceB844 + difference 5 1) sourceC844) = raw13998 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw13998; decide +kernel
    rw [ha]
    exact (canonical13998 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA844 + difference 2 0) (sourceB844 + difference 0 2) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA844 + difference 2 0) (sourceB844 + difference 0 2) sourceC844) = raw13999 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw13999; decide +kernel
    rw [ha]
    exact (canonical13999 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA844 + difference 2 1) (sourceB844 + difference 1 2) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2503) := by
    have ha : (tripleCharges (sourceA844 + difference 2 1) (sourceB844 + difference 1 2) sourceC844) = raw14000 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14000; decide +kernel
    rw [ha]
    exact (canonical14000 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA844 + difference 2 3) (sourceB844 + difference 3 2) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA844 + difference 2 3) (sourceB844 + difference 3 2) sourceC844) = raw8046 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw8046; decide +kernel
    rw [ha]
    exact (canonical8046 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA844 + difference 2 4) (sourceB844 + difference 4 2) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA844 + difference 2 4) (sourceB844 + difference 4 2) sourceC844) = raw14001 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14001; decide +kernel
    rw [ha]
    exact (canonical14001 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA844 + difference 2 5) (sourceB844 + difference 5 2) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA844 + difference 2 5) (sourceB844 + difference 5 2) sourceC844) = raw14002 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14002; decide +kernel
    rw [ha]
    exact (canonical14002 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA844 + difference 3 0) (sourceB844 + difference 0 3) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA844 + difference 3 0) (sourceB844 + difference 0 3) sourceC844) = raw14003 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14003; decide +kernel
    rw [ha]
    exact (canonical14003 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA844 + difference 3 1) (sourceB844 + difference 1 3) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2504) := by
    have ha : (tripleCharges (sourceA844 + difference 3 1) (sourceB844 + difference 1 3) sourceC844) = raw14004 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14004; decide +kernel
    rw [ha]
    exact (canonical14004 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA844 + difference 3 2) (sourceB844 + difference 2 3) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2504) := by
    have ha : (tripleCharges (sourceA844 + difference 3 2) (sourceB844 + difference 2 3) sourceC844) = raw14005 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14005; decide +kernel
    rw [ha]
    exact (canonical14005 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA844 + difference 3 4) (sourceB844 + difference 4 3) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA844 + difference 3 4) (sourceB844 + difference 4 3) sourceC844) = raw14006 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14006; decide +kernel
    rw [ha]
    exact (canonical14006 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA844 + difference 3 5) (sourceB844 + difference 5 3) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA844 + difference 3 5) (sourceB844 + difference 5 3) sourceC844) = raw14007 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14007; decide +kernel
    rw [ha]
    exact (canonical14007 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA844 + difference 4 0) (sourceB844 + difference 0 4) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA844 + difference 4 0) (sourceB844 + difference 0 4) sourceC844) = raw14008 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14008; decide +kernel
    rw [ha]
    exact (canonical14008 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA844 + difference 4 1) (sourceB844 + difference 1 4) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA844 + difference 4 1) (sourceB844 + difference 1 4) sourceC844) = raw14009 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14009; decide +kernel
    rw [ha]
    exact (canonical14009 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA844 + difference 4 2) (sourceB844 + difference 2 4) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA844 + difference 4 2) (sourceB844 + difference 2 4) sourceC844) = raw14010 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14010; decide +kernel
    rw [ha]
    exact (canonical14010 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA844 + difference 4 3) (sourceB844 + difference 3 4) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA844 + difference 4 3) (sourceB844 + difference 3 4) sourceC844) = raw8056 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw8056; decide +kernel
    rw [ha]
    exact (canonical8056 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA844 + difference 4 5) (sourceB844 + difference 5 4) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA844 + difference 4 5) (sourceB844 + difference 5 4) sourceC844) = raw14011 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14011; decide +kernel
    rw [ha]
    exact (canonical14011 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA844 + difference 5 0) (sourceB844 + difference 0 5) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA844 + difference 5 0) (sourceB844 + difference 0 5) sourceC844) = raw8047 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw8047; decide +kernel
    rw [ha]
    exact (canonical8047 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA844 + difference 5 1) (sourceB844 + difference 1 5) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA844 + difference 5 1) (sourceB844 + difference 1 5) sourceC844) = raw8048 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw8048; decide +kernel
    rw [ha]
    exact (canonical8048 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA844 + difference 5 2) (sourceB844 + difference 2 5) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA844 + difference 5 2) (sourceB844 + difference 2 5) sourceC844) = raw8049 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw8049; decide +kernel
    rw [ha]
    exact (canonical8049 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA844 + difference 5 3) (sourceB844 + difference 3 5) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA844 + difference 5 3) (sourceB844 + difference 3 5) sourceC844) = raw14012 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw14012; decide +kernel
    rw [ha]
    exact (canonical14012 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA844 + difference 5 4) (sourceB844 + difference 4 5) sourceC844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA844 + difference 5 4) (sourceB844 + difference 4 5) sourceC844) = raw8050 := by
      apply Matrix.ext; unfold tripleCharges sourceA844 sourceB844 sourceC844 difference raw8050; decide +kernel
    rw [ha]
    exact (canonical8050 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA844 sourceB844 sourceC844
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm844, Integer.Sparse.eval]
  linarith only [hs]

def sourceA845 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB845 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC845 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm845 : Integer.Sparse Master := [(Sum.inr 4866, 2), (Sum.inr 4871, 1), (Sum.inr 4875, 1), (Sum.inr 4895, 1), (Sum.inr 5173, 2), (Sum.inr 5175, 1), (Sum.inr 5255, 2), (Sum.inr 5269, 2), (Sum.inr 5271, 2), (Sum.inr 5288, 2), (Sum.inr 5289, 4), (Sum.inr 5290, 2), (Sum.inr 5295, 2), (Sum.inr 5303, 1), (Sum.inr 5304, 2), (Sum.inr 5306, 2), (Sum.inr 5307, 1)]

theorem sourceEq845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm845 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA845 + difference 0 1) (sourceB845 + difference 1 0) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA845 + difference 0 1) (sourceB845 + difference 1 0) sourceC845) = raw14013 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14013; decide +kernel
    rw [ha]
    exact (canonical14013 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA845 + difference 0 2) (sourceB845 + difference 2 0) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA845 + difference 0 2) (sourceB845 + difference 2 0) sourceC845) = raw14014 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14014; decide +kernel
    rw [ha]
    exact (canonical14014 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA845 + difference 0 3) (sourceB845 + difference 3 0) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA845 + difference 0 3) (sourceB845 + difference 3 0) sourceC845) = raw13617 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw13617; decide +kernel
    rw [ha]
    exact (canonical13617 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA845 + difference 0 4) (sourceB845 + difference 4 0) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA845 + difference 0 4) (sourceB845 + difference 4 0) sourceC845) = raw14015 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14015; decide +kernel
    rw [ha]
    exact (canonical14015 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA845 + difference 0 5) (sourceB845 + difference 5 0) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA845 + difference 0 5) (sourceB845 + difference 5 0) sourceC845) = raw14016 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14016; decide +kernel
    rw [ha]
    exact (canonical14016 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA845 + difference 1 0) (sourceB845 + difference 0 1) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA845 + difference 1 0) (sourceB845 + difference 0 1) sourceC845) = raw13630 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw13630; decide +kernel
    rw [ha]
    exact (canonical13630 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA845 + difference 1 2) (sourceB845 + difference 2 1) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA845 + difference 1 2) (sourceB845 + difference 2 1) sourceC845) = raw13632 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw13632; decide +kernel
    rw [ha]
    exact (canonical13632 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA845 + difference 1 3) (sourceB845 + difference 3 1) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA845 + difference 1 3) (sourceB845 + difference 3 1) sourceC845) = raw13843 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw13843; decide +kernel
    rw [ha]
    exact (canonical13843 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA845 + difference 1 4) (sourceB845 + difference 4 1) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA845 + difference 1 4) (sourceB845 + difference 4 1) sourceC845) = raw13633 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw13633; decide +kernel
    rw [ha]
    exact (canonical13633 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA845 + difference 1 5) (sourceB845 + difference 5 1) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA845 + difference 1 5) (sourceB845 + difference 5 1) sourceC845) = raw13634 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw13634; decide +kernel
    rw [ha]
    exact (canonical13634 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA845 + difference 2 0) (sourceB845 + difference 0 2) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA845 + difference 2 0) (sourceB845 + difference 0 2) sourceC845) = raw14017 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14017; decide +kernel
    rw [ha]
    exact (canonical14017 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA845 + difference 2 1) (sourceB845 + difference 1 2) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA845 + difference 2 1) (sourceB845 + difference 1 2) sourceC845) = raw14018 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14018; decide +kernel
    rw [ha]
    exact (canonical14018 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA845 + difference 2 3) (sourceB845 + difference 3 2) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA845 + difference 2 3) (sourceB845 + difference 3 2) sourceC845) = raw13628 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw13628; decide +kernel
    rw [ha]
    exact (canonical13628 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA845 + difference 2 4) (sourceB845 + difference 4 2) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA845 + difference 2 4) (sourceB845 + difference 4 2) sourceC845) = raw14019 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14019; decide +kernel
    rw [ha]
    exact (canonical14019 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA845 + difference 2 5) (sourceB845 + difference 5 2) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA845 + difference 2 5) (sourceB845 + difference 5 2) sourceC845) = raw14020 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14020; decide +kernel
    rw [ha]
    exact (canonical14020 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA845 + difference 3 0) (sourceB845 + difference 0 3) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA845 + difference 3 0) (sourceB845 + difference 0 3) sourceC845) = raw14021 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14021; decide +kernel
    rw [ha]
    exact (canonical14021 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA845 + difference 3 1) (sourceB845 + difference 1 3) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA845 + difference 3 1) (sourceB845 + difference 1 3) sourceC845) = raw14022 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14022; decide +kernel
    rw [ha]
    exact (canonical14022 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA845 + difference 3 2) (sourceB845 + difference 2 3) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA845 + difference 3 2) (sourceB845 + difference 2 3) sourceC845) = raw14023 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14023; decide +kernel
    rw [ha]
    exact (canonical14023 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA845 + difference 3 4) (sourceB845 + difference 4 3) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA845 + difference 3 4) (sourceB845 + difference 4 3) sourceC845) = raw14024 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14024; decide +kernel
    rw [ha]
    exact (canonical14024 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA845 + difference 3 5) (sourceB845 + difference 5 3) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA845 + difference 3 5) (sourceB845 + difference 5 3) sourceC845) = raw14025 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14025; decide +kernel
    rw [ha]
    exact (canonical14025 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA845 + difference 4 0) (sourceB845 + difference 0 4) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA845 + difference 4 0) (sourceB845 + difference 0 4) sourceC845) = raw14026 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14026; decide +kernel
    rw [ha]
    exact (canonical14026 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA845 + difference 4 1) (sourceB845 + difference 1 4) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA845 + difference 4 1) (sourceB845 + difference 1 4) sourceC845) = raw14027 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14027; decide +kernel
    rw [ha]
    exact (canonical14027 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA845 + difference 4 2) (sourceB845 + difference 2 4) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA845 + difference 4 2) (sourceB845 + difference 2 4) sourceC845) = raw14028 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14028; decide +kernel
    rw [ha]
    exact (canonical14028 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA845 + difference 4 3) (sourceB845 + difference 3 4) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA845 + difference 4 3) (sourceB845 + difference 3 4) sourceC845) = raw13636 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw13636; decide +kernel
    rw [ha]
    exact (canonical13636 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA845 + difference 4 5) (sourceB845 + difference 5 4) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5303) := by
    have ha : (tripleCharges (sourceA845 + difference 4 5) (sourceB845 + difference 5 4) sourceC845) = raw14029 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14029; decide +kernel
    rw [ha]
    exact (canonical14029 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA845 + difference 5 0) (sourceB845 + difference 0 5) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA845 + difference 5 0) (sourceB845 + difference 0 5) sourceC845) = raw14030 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14030; decide +kernel
    rw [ha]
    exact (canonical14030 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA845 + difference 5 1) (sourceB845 + difference 1 5) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA845 + difference 5 1) (sourceB845 + difference 1 5) sourceC845) = raw14031 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14031; decide +kernel
    rw [ha]
    exact (canonical14031 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA845 + difference 5 2) (sourceB845 + difference 2 5) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA845 + difference 5 2) (sourceB845 + difference 2 5) sourceC845) = raw13845 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw13845; decide +kernel
    rw [ha]
    exact (canonical13845 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA845 + difference 5 3) (sourceB845 + difference 3 5) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA845 + difference 5 3) (sourceB845 + difference 3 5) sourceC845) = raw13641 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw13641; decide +kernel
    rw [ha]
    exact (canonical13641 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA845 + difference 5 4) (sourceB845 + difference 4 5) sourceC845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA845 + difference 5 4) (sourceB845 + difference 4 5) sourceC845) = raw14032 := by
      apply Matrix.ext; unfold tripleCharges sourceA845 sourceB845 sourceC845 difference raw14032; decide +kernel
    rw [ha]
    exact (canonical14032 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA845 sourceB845 sourceC845
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm845, Integer.Sparse.eval]
  linarith only [hs]

def sourceA846 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB846 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC846 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm846 : Integer.Sparse Master := [(Sum.inr 2260, 2), (Sum.inr 2287, 1), (Sum.inr 2288, 1), (Sum.inr 2291, 1), (Sum.inr 2718, 2), (Sum.inr 2735, 2), (Sum.inr 2736, 2), (Sum.inr 2739, 2), (Sum.inr 2760, 2), (Sum.inr 2761, 1), (Sum.inr 2763, 2), (Sum.inr 2764, 2), (Sum.inr 2769, 1), (Sum.inr 2779, 1), (Sum.inr 2781, 1), (Sum.inr 2782, 1), (Sum.inr 2784, 1), (Sum.inr 2785, 1), (Sum.inr 3097, 2), (Sum.inr 3119, 1), (Sum.inr 3120, 1)]

theorem sourceEq846 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm846 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA846 + difference 0 1) (sourceB846 + difference 1 0) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA846 + difference 0 1) (sourceB846 + difference 1 0) sourceC846) = raw14033 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14033; decide +kernel
    rw [ha]
    exact (canonical14033 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA846 + difference 0 2) (sourceB846 + difference 2 0) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA846 + difference 0 2) (sourceB846 + difference 2 0) sourceC846) = raw14034 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14034; decide +kernel
    rw [ha]
    exact (canonical14034 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA846 + difference 0 3) (sourceB846 + difference 3 0) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA846 + difference 0 3) (sourceB846 + difference 3 0) sourceC846) = raw13643 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw13643; decide +kernel
    rw [ha]
    exact (canonical13643 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA846 + difference 0 4) (sourceB846 + difference 4 0) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA846 + difference 0 4) (sourceB846 + difference 4 0) sourceC846) = raw14035 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14035; decide +kernel
    rw [ha]
    exact (canonical14035 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA846 + difference 0 5) (sourceB846 + difference 5 0) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA846 + difference 0 5) (sourceB846 + difference 5 0) sourceC846) = raw14036 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14036; decide +kernel
    rw [ha]
    exact (canonical14036 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA846 + difference 1 0) (sourceB846 + difference 0 1) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA846 + difference 1 0) (sourceB846 + difference 0 1) sourceC846) = raw13658 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw13658; decide +kernel
    rw [ha]
    exact (canonical13658 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA846 + difference 1 2) (sourceB846 + difference 2 1) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA846 + difference 1 2) (sourceB846 + difference 2 1) sourceC846) = raw13660 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw13660; decide +kernel
    rw [ha]
    exact (canonical13660 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA846 + difference 1 3) (sourceB846 + difference 3 1) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA846 + difference 1 3) (sourceB846 + difference 3 1) sourceC846) = raw13865 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw13865; decide +kernel
    rw [ha]
    exact (canonical13865 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA846 + difference 1 4) (sourceB846 + difference 4 1) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA846 + difference 1 4) (sourceB846 + difference 4 1) sourceC846) = raw13661 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw13661; decide +kernel
    rw [ha]
    exact (canonical13661 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA846 + difference 1 5) (sourceB846 + difference 5 1) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA846 + difference 1 5) (sourceB846 + difference 5 1) sourceC846) = raw13662 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw13662; decide +kernel
    rw [ha]
    exact (canonical13662 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA846 + difference 2 0) (sourceB846 + difference 0 2) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA846 + difference 2 0) (sourceB846 + difference 0 2) sourceC846) = raw14037 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14037; decide +kernel
    rw [ha]
    exact (canonical14037 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA846 + difference 2 1) (sourceB846 + difference 1 2) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA846 + difference 2 1) (sourceB846 + difference 1 2) sourceC846) = raw14038 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14038; decide +kernel
    rw [ha]
    exact (canonical14038 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA846 + difference 2 3) (sourceB846 + difference 3 2) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA846 + difference 2 3) (sourceB846 + difference 3 2) sourceC846) = raw13654 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw13654; decide +kernel
    rw [ha]
    exact (canonical13654 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA846 + difference 2 4) (sourceB846 + difference 4 2) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA846 + difference 2 4) (sourceB846 + difference 4 2) sourceC846) = raw14039 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14039; decide +kernel
    rw [ha]
    exact (canonical14039 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA846 + difference 2 5) (sourceB846 + difference 5 2) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA846 + difference 2 5) (sourceB846 + difference 5 2) sourceC846) = raw14040 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14040; decide +kernel
    rw [ha]
    exact (canonical14040 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA846 + difference 3 0) (sourceB846 + difference 0 3) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA846 + difference 3 0) (sourceB846 + difference 0 3) sourceC846) = raw14041 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14041; decide +kernel
    rw [ha]
    exact (canonical14041 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA846 + difference 3 1) (sourceB846 + difference 1 3) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA846 + difference 3 1) (sourceB846 + difference 1 3) sourceC846) = raw14042 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14042; decide +kernel
    rw [ha]
    exact (canonical14042 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA846 + difference 3 2) (sourceB846 + difference 2 3) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA846 + difference 3 2) (sourceB846 + difference 2 3) sourceC846) = raw14043 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14043; decide +kernel
    rw [ha]
    exact (canonical14043 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA846 + difference 3 4) (sourceB846 + difference 4 3) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA846 + difference 3 4) (sourceB846 + difference 4 3) sourceC846) = raw14044 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14044; decide +kernel
    rw [ha]
    exact (canonical14044 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA846 + difference 3 5) (sourceB846 + difference 5 3) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA846 + difference 3 5) (sourceB846 + difference 5 3) sourceC846) = raw14045 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14045; decide +kernel
    rw [ha]
    exact (canonical14045 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA846 + difference 4 0) (sourceB846 + difference 0 4) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA846 + difference 4 0) (sourceB846 + difference 0 4) sourceC846) = raw14046 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14046; decide +kernel
    rw [ha]
    exact (canonical14046 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA846 + difference 4 1) (sourceB846 + difference 1 4) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA846 + difference 4 1) (sourceB846 + difference 1 4) sourceC846) = raw14047 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14047; decide +kernel
    rw [ha]
    exact (canonical14047 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA846 + difference 4 2) (sourceB846 + difference 2 4) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA846 + difference 4 2) (sourceB846 + difference 2 4) sourceC846) = raw14048 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14048; decide +kernel
    rw [ha]
    exact (canonical14048 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA846 + difference 4 3) (sourceB846 + difference 3 4) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA846 + difference 4 3) (sourceB846 + difference 3 4) sourceC846) = raw13664 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw13664; decide +kernel
    rw [ha]
    exact (canonical13664 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA846 + difference 4 5) (sourceB846 + difference 5 4) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2779) := by
    have ha : (tripleCharges (sourceA846 + difference 4 5) (sourceB846 + difference 5 4) sourceC846) = raw14049 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14049; decide +kernel
    rw [ha]
    exact (canonical14049 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA846 + difference 5 0) (sourceB846 + difference 0 5) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA846 + difference 5 0) (sourceB846 + difference 0 5) sourceC846) = raw14050 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14050; decide +kernel
    rw [ha]
    exact (canonical14050 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA846 + difference 5 1) (sourceB846 + difference 1 5) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA846 + difference 5 1) (sourceB846 + difference 1 5) sourceC846) = raw14051 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14051; decide +kernel
    rw [ha]
    exact (canonical14051 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA846 + difference 5 2) (sourceB846 + difference 2 5) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA846 + difference 5 2) (sourceB846 + difference 2 5) sourceC846) = raw13867 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw13867; decide +kernel
    rw [ha]
    exact (canonical13867 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA846 + difference 5 3) (sourceB846 + difference 3 5) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2785) := by
    have ha : (tripleCharges (sourceA846 + difference 5 3) (sourceB846 + difference 3 5) sourceC846) = raw13669 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw13669; decide +kernel
    rw [ha]
    exact (canonical13669 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA846 + difference 5 4) (sourceB846 + difference 4 5) sourceC846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA846 + difference 5 4) (sourceB846 + difference 4 5) sourceC846) = raw14052 := by
      apply Matrix.ext; unfold tripleCharges sourceA846 sourceB846 sourceC846 difference raw14052; decide +kernel
    rw [ha]
    exact (canonical14052 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA846 sourceB846 sourceC846
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm846, Integer.Sparse.eval]
  linarith only [hs]

def sourceA847 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB847 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC847 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm847 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 4622, 2), (Sum.inr 4623, 1), (Sum.inr 4624, 2), (Sum.inr 5167, 2), (Sum.inr 5169, 4), (Sum.inr 5172, 2), (Sum.inr 5292, 4), (Sum.inr 5293, 2), (Sum.inr 5294, 2), (Sum.inr 5307, 2), (Sum.inr 5309, 2), (Sum.inr 5440, 2), (Sum.inr 5454, 2)]

theorem sourceEq847 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm847 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA847 + difference 0 1) (sourceB847 + difference 1 0) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA847 + difference 0 1) (sourceB847 + difference 1 0) sourceC847) = raw14053 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14053; decide +kernel
    rw [ha]
    exact (canonical14053 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA847 + difference 0 2) (sourceB847 + difference 2 0) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA847 + difference 0 2) (sourceB847 + difference 2 0) sourceC847) = raw14054 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14054; decide +kernel
    rw [ha]
    exact (canonical14054 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA847 + difference 0 3) (sourceB847 + difference 3 0) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA847 + difference 0 3) (sourceB847 + difference 3 0) sourceC847) = raw2685 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw2685; decide +kernel
    rw [ha]
    exact (canonical2685 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA847 + difference 0 4) (sourceB847 + difference 4 0) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA847 + difference 0 4) (sourceB847 + difference 4 0) sourceC847) = raw2680 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw2680; decide +kernel
    rw [ha]
    exact (canonical2680 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA847 + difference 0 5) (sourceB847 + difference 5 0) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA847 + difference 0 5) (sourceB847 + difference 5 0) sourceC847) = raw14055 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14055; decide +kernel
    rw [ha]
    exact (canonical14055 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA847 + difference 1 0) (sourceB847 + difference 0 1) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA847 + difference 1 0) (sourceB847 + difference 0 1) sourceC847) = raw14056 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14056; decide +kernel
    rw [ha]
    exact (canonical14056 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA847 + difference 1 2) (sourceB847 + difference 2 1) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA847 + difference 1 2) (sourceB847 + difference 2 1) sourceC847) = raw14057 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14057; decide +kernel
    rw [ha]
    exact (canonical14057 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA847 + difference 1 3) (sourceB847 + difference 3 1) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA847 + difference 1 3) (sourceB847 + difference 3 1) sourceC847) = raw7971 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw7971; decide +kernel
    rw [ha]
    exact (canonical7971 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA847 + difference 1 4) (sourceB847 + difference 4 1) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA847 + difference 1 4) (sourceB847 + difference 4 1) sourceC847) = raw14058 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14058; decide +kernel
    rw [ha]
    exact (canonical14058 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA847 + difference 1 5) (sourceB847 + difference 5 1) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA847 + difference 1 5) (sourceB847 + difference 5 1) sourceC847) = raw14059 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14059; decide +kernel
    rw [ha]
    exact (canonical14059 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA847 + difference 2 0) (sourceB847 + difference 0 2) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA847 + difference 2 0) (sourceB847 + difference 0 2) sourceC847) = raw14060 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14060; decide +kernel
    rw [ha]
    exact (canonical14060 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA847 + difference 2 1) (sourceB847 + difference 1 2) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA847 + difference 2 1) (sourceB847 + difference 1 2) sourceC847) = raw14061 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14061; decide +kernel
    rw [ha]
    exact (canonical14061 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA847 + difference 2 3) (sourceB847 + difference 3 2) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA847 + difference 2 3) (sourceB847 + difference 3 2) sourceC847) = raw7975 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw7975; decide +kernel
    rw [ha]
    exact (canonical7975 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA847 + difference 2 4) (sourceB847 + difference 4 2) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA847 + difference 2 4) (sourceB847 + difference 4 2) sourceC847) = raw14062 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14062; decide +kernel
    rw [ha]
    exact (canonical14062 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA847 + difference 2 5) (sourceB847 + difference 5 2) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA847 + difference 2 5) (sourceB847 + difference 5 2) sourceC847) = raw14063 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14063; decide +kernel
    rw [ha]
    exact (canonical14063 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA847 + difference 3 0) (sourceB847 + difference 0 3) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA847 + difference 3 0) (sourceB847 + difference 0 3) sourceC847) = raw14064 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14064; decide +kernel
    rw [ha]
    exact (canonical14064 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA847 + difference 3 1) (sourceB847 + difference 1 3) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA847 + difference 3 1) (sourceB847 + difference 1 3) sourceC847) = raw14065 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14065; decide +kernel
    rw [ha]
    exact (canonical14065 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA847 + difference 3 2) (sourceB847 + difference 2 3) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA847 + difference 3 2) (sourceB847 + difference 2 3) sourceC847) = raw14066 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14066; decide +kernel
    rw [ha]
    exact (canonical14066 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA847 + difference 3 4) (sourceB847 + difference 4 3) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA847 + difference 3 4) (sourceB847 + difference 4 3) sourceC847) = raw14067 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14067; decide +kernel
    rw [ha]
    exact (canonical14067 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA847 + difference 3 5) (sourceB847 + difference 5 3) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA847 + difference 3 5) (sourceB847 + difference 5 3) sourceC847) = raw14068 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14068; decide +kernel
    rw [ha]
    exact (canonical14068 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA847 + difference 4 0) (sourceB847 + difference 0 4) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA847 + difference 4 0) (sourceB847 + difference 0 4) sourceC847) = raw14069 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14069; decide +kernel
    rw [ha]
    exact (canonical14069 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA847 + difference 4 1) (sourceB847 + difference 1 4) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA847 + difference 4 1) (sourceB847 + difference 1 4) sourceC847) = raw14070 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14070; decide +kernel
    rw [ha]
    exact (canonical14070 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA847 + difference 4 2) (sourceB847 + difference 2 4) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA847 + difference 4 2) (sourceB847 + difference 2 4) sourceC847) = raw14071 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14071; decide +kernel
    rw [ha]
    exact (canonical14071 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA847 + difference 4 3) (sourceB847 + difference 3 4) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA847 + difference 4 3) (sourceB847 + difference 3 4) sourceC847) = raw7984 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw7984; decide +kernel
    rw [ha]
    exact (canonical7984 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA847 + difference 4 5) (sourceB847 + difference 5 4) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA847 + difference 4 5) (sourceB847 + difference 5 4) sourceC847) = raw14072 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw14072; decide +kernel
    rw [ha]
    exact (canonical14072 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA847 + difference 5 0) (sourceB847 + difference 0 5) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA847 + difference 5 0) (sourceB847 + difference 0 5) sourceC847) = raw7976 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw7976; decide +kernel
    rw [ha]
    exact (canonical7976 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA847 + difference 5 1) (sourceB847 + difference 1 5) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA847 + difference 5 1) (sourceB847 + difference 1 5) sourceC847) = raw7977 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw7977; decide +kernel
    rw [ha]
    exact (canonical7977 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA847 + difference 5 2) (sourceB847 + difference 2 5) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA847 + difference 5 2) (sourceB847 + difference 2 5) sourceC847) = raw7978 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw7978; decide +kernel
    rw [ha]
    exact (canonical7978 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA847 + difference 5 3) (sourceB847 + difference 3 5) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA847 + difference 5 3) (sourceB847 + difference 3 5) sourceC847) = raw2681 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw2681; decide +kernel
    rw [ha]
    exact (canonical2681 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA847 + difference 5 4) (sourceB847 + difference 4 5) sourceC847) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA847 + difference 5 4) (sourceB847 + difference 4 5) sourceC847) = raw2676 := by
      apply Matrix.ext; unfold tripleCharges sourceA847 sourceB847 sourceC847 difference raw2676; decide +kernel
    rw [ha]
    exact (canonical2676 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA847 sourceB847 sourceC847
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm847, Integer.Sparse.eval]
  linarith only [hs]

def sourceA848 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB848 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC848 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceForm848 : Integer.Sparse Master := [(Sum.inr 4599, 1), (Sum.inr 4602, 1), (Sum.inr 4603, 1), (Sum.inr 4607, 1), (Sum.inr 4616, 1), (Sum.inr 5098, 1), (Sum.inr 5101, 1), (Sum.inr 5102, 1), (Sum.inr 5105, 1), (Sum.inr 5134, 1), (Sum.inr 5135, 1), (Sum.inr 5138, 1), (Sum.inr 5160, 1), (Sum.inr 5256, 1), (Sum.inr 5258, 1), (Sum.inr 5260, 1), (Sum.inr 5265, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5271, 1), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5289, 1), (Sum.inr 5299, 1), (Sum.inr 5304, 1), (Sum.inr 5410, 1), (Sum.inr 5424, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5442, 1)]

theorem sourceEq848 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm848 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA848 + difference 0 1) (sourceB848 + difference 1 0) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA848 + difference 0 1) (sourceB848 + difference 1 0) sourceC848) = raw14073 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14073; decide +kernel
    rw [ha]
    exact (canonical14073 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA848 + difference 0 2) (sourceB848 + difference 2 0) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA848 + difference 0 2) (sourceB848 + difference 2 0) sourceC848) = raw14074 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14074; decide +kernel
    rw [ha]
    exact (canonical14074 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA848 + difference 0 3) (sourceB848 + difference 3 0) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA848 + difference 0 3) (sourceB848 + difference 3 0) sourceC848) = raw14075 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14075; decide +kernel
    rw [ha]
    exact (canonical14075 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA848 + difference 0 4) (sourceB848 + difference 4 0) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA848 + difference 0 4) (sourceB848 + difference 4 0) sourceC848) = raw14076 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14076; decide +kernel
    rw [ha]
    exact (canonical14076 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA848 + difference 0 5) (sourceB848 + difference 5 0) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA848 + difference 0 5) (sourceB848 + difference 5 0) sourceC848) = raw14077 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14077; decide +kernel
    rw [ha]
    exact (canonical14077 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA848 + difference 1 0) (sourceB848 + difference 0 1) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA848 + difference 1 0) (sourceB848 + difference 0 1) sourceC848) = raw14078 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14078; decide +kernel
    rw [ha]
    exact (canonical14078 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA848 + difference 1 2) (sourceB848 + difference 2 1) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA848 + difference 1 2) (sourceB848 + difference 2 1) sourceC848) = raw14079 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14079; decide +kernel
    rw [ha]
    exact (canonical14079 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA848 + difference 1 3) (sourceB848 + difference 3 1) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA848 + difference 1 3) (sourceB848 + difference 3 1) sourceC848) = raw14080 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14080; decide +kernel
    rw [ha]
    exact (canonical14080 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA848 + difference 1 4) (sourceB848 + difference 4 1) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA848 + difference 1 4) (sourceB848 + difference 4 1) sourceC848) = raw14081 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14081; decide +kernel
    rw [ha]
    exact (canonical14081 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA848 + difference 1 5) (sourceB848 + difference 5 1) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA848 + difference 1 5) (sourceB848 + difference 5 1) sourceC848) = raw14082 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14082; decide +kernel
    rw [ha]
    exact (canonical14082 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA848 + difference 2 0) (sourceB848 + difference 0 2) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA848 + difference 2 0) (sourceB848 + difference 0 2) sourceC848) = raw14083 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14083; decide +kernel
    rw [ha]
    exact (canonical14083 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA848 + difference 2 1) (sourceB848 + difference 1 2) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA848 + difference 2 1) (sourceB848 + difference 1 2) sourceC848) = raw14084 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14084; decide +kernel
    rw [ha]
    exact (canonical14084 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA848 + difference 2 3) (sourceB848 + difference 3 2) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA848 + difference 2 3) (sourceB848 + difference 3 2) sourceC848) = raw14085 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14085; decide +kernel
    rw [ha]
    exact (canonical14085 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA848 + difference 2 4) (sourceB848 + difference 4 2) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA848 + difference 2 4) (sourceB848 + difference 4 2) sourceC848) = raw14086 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14086; decide +kernel
    rw [ha]
    exact (canonical14086 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA848 + difference 2 5) (sourceB848 + difference 5 2) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA848 + difference 2 5) (sourceB848 + difference 5 2) sourceC848) = raw14087 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14087; decide +kernel
    rw [ha]
    exact (canonical14087 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA848 + difference 3 0) (sourceB848 + difference 0 3) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA848 + difference 3 0) (sourceB848 + difference 0 3) sourceC848) = raw14088 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14088; decide +kernel
    rw [ha]
    exact (canonical14088 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA848 + difference 3 1) (sourceB848 + difference 1 3) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA848 + difference 3 1) (sourceB848 + difference 1 3) sourceC848) = raw14089 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14089; decide +kernel
    rw [ha]
    exact (canonical14089 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA848 + difference 3 2) (sourceB848 + difference 2 3) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA848 + difference 3 2) (sourceB848 + difference 2 3) sourceC848) = raw14090 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14090; decide +kernel
    rw [ha]
    exact (canonical14090 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA848 + difference 3 4) (sourceB848 + difference 4 3) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA848 + difference 3 4) (sourceB848 + difference 4 3) sourceC848) = raw14091 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14091; decide +kernel
    rw [ha]
    exact (canonical14091 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA848 + difference 3 5) (sourceB848 + difference 5 3) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA848 + difference 3 5) (sourceB848 + difference 5 3) sourceC848) = raw14092 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14092; decide +kernel
    rw [ha]
    exact (canonical14092 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA848 + difference 4 0) (sourceB848 + difference 0 4) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA848 + difference 4 0) (sourceB848 + difference 0 4) sourceC848) = raw14093 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14093; decide +kernel
    rw [ha]
    exact (canonical14093 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA848 + difference 4 1) (sourceB848 + difference 1 4) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA848 + difference 4 1) (sourceB848 + difference 1 4) sourceC848) = raw14094 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14094; decide +kernel
    rw [ha]
    exact (canonical14094 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA848 + difference 4 2) (sourceB848 + difference 2 4) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA848 + difference 4 2) (sourceB848 + difference 2 4) sourceC848) = raw14095 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14095; decide +kernel
    rw [ha]
    exact (canonical14095 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA848 + difference 4 3) (sourceB848 + difference 3 4) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA848 + difference 4 3) (sourceB848 + difference 3 4) sourceC848) = raw14096 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14096; decide +kernel
    rw [ha]
    exact (canonical14096 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA848 + difference 4 5) (sourceB848 + difference 5 4) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA848 + difference 4 5) (sourceB848 + difference 5 4) sourceC848) = raw14097 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14097; decide +kernel
    rw [ha]
    exact (canonical14097 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA848 + difference 5 0) (sourceB848 + difference 0 5) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA848 + difference 5 0) (sourceB848 + difference 0 5) sourceC848) = raw14098 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14098; decide +kernel
    rw [ha]
    exact (canonical14098 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA848 + difference 5 1) (sourceB848 + difference 1 5) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA848 + difference 5 1) (sourceB848 + difference 1 5) sourceC848) = raw14099 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14099; decide +kernel
    rw [ha]
    exact (canonical14099 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA848 + difference 5 2) (sourceB848 + difference 2 5) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA848 + difference 5 2) (sourceB848 + difference 2 5) sourceC848) = raw14100 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14100; decide +kernel
    rw [ha]
    exact (canonical14100 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA848 + difference 5 3) (sourceB848 + difference 3 5) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA848 + difference 5 3) (sourceB848 + difference 3 5) sourceC848) = raw14101 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14101; decide +kernel
    rw [ha]
    exact (canonical14101 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA848 + difference 5 4) (sourceB848 + difference 4 5) sourceC848) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA848 + difference 5 4) (sourceB848 + difference 4 5) sourceC848) = raw14102 := by
      apply Matrix.ext; unfold tripleCharges sourceA848 sourceB848 sourceC848 difference raw14102; decide +kernel
    rw [ha]
    exact (canonical14102 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA848 sourceB848 sourceC848
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm848, Integer.Sparse.eval]
  linarith only [hs]

def sourceA849 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB849 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC849 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceForm849 : Integer.Sparse Master := [(Sum.inr 3289, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 3296, 1), (Sum.inr 3303, 1), (Sum.inr 3460, 1), (Sum.inr 3470, 1), (Sum.inr 3471, 1), (Sum.inr 3479, 1), (Sum.inr 3514, 1), (Sum.inr 3515, 1), (Sum.inr 3517, 1), (Sum.inr 3525, 1), (Sum.inr 3526, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3535, 1), (Sum.inr 3540, 1), (Sum.inr 3541, 1), (Sum.inr 3547, 1), (Sum.inr 3548, 1), (Sum.inr 3558, 1), (Sum.inr 3572, 1), (Sum.inr 3573, 1), (Sum.inr 3583, 1), (Sum.inr 3808, 1), (Sum.inr 3838, 1), (Sum.inr 3852, 1), (Sum.inr 3853, 1), (Sum.inr 3861, 1)]

theorem sourceEq849 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm849 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA849 + difference 0 1) (sourceB849 + difference 1 0) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA849 + difference 0 1) (sourceB849 + difference 1 0) sourceC849) = raw14103 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14103; decide +kernel
    rw [ha]
    exact (canonical14103 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA849 + difference 0 2) (sourceB849 + difference 2 0) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA849 + difference 0 2) (sourceB849 + difference 2 0) sourceC849) = raw14104 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14104; decide +kernel
    rw [ha]
    exact (canonical14104 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA849 + difference 0 3) (sourceB849 + difference 3 0) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA849 + difference 0 3) (sourceB849 + difference 3 0) sourceC849) = raw14105 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14105; decide +kernel
    rw [ha]
    exact (canonical14105 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA849 + difference 0 4) (sourceB849 + difference 4 0) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA849 + difference 0 4) (sourceB849 + difference 4 0) sourceC849) = raw14106 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14106; decide +kernel
    rw [ha]
    exact (canonical14106 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA849 + difference 0 5) (sourceB849 + difference 5 0) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3861) := by
    have ha : (tripleCharges (sourceA849 + difference 0 5) (sourceB849 + difference 5 0) sourceC849) = raw14107 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14107; decide +kernel
    rw [ha]
    exact (canonical14107 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA849 + difference 1 0) (sourceB849 + difference 0 1) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA849 + difference 1 0) (sourceB849 + difference 0 1) sourceC849) = raw14108 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14108; decide +kernel
    rw [ha]
    exact (canonical14108 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA849 + difference 1 2) (sourceB849 + difference 2 1) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA849 + difference 1 2) (sourceB849 + difference 2 1) sourceC849) = raw14109 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14109; decide +kernel
    rw [ha]
    exact (canonical14109 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA849 + difference 1 3) (sourceB849 + difference 3 1) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA849 + difference 1 3) (sourceB849 + difference 3 1) sourceC849) = raw14110 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14110; decide +kernel
    rw [ha]
    exact (canonical14110 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA849 + difference 1 4) (sourceB849 + difference 4 1) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA849 + difference 1 4) (sourceB849 + difference 4 1) sourceC849) = raw14111 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14111; decide +kernel
    rw [ha]
    exact (canonical14111 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA849 + difference 1 5) (sourceB849 + difference 5 1) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA849 + difference 1 5) (sourceB849 + difference 5 1) sourceC849) = raw14112 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14112; decide +kernel
    rw [ha]
    exact (canonical14112 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA849 + difference 2 0) (sourceB849 + difference 0 2) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA849 + difference 2 0) (sourceB849 + difference 0 2) sourceC849) = raw14113 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14113; decide +kernel
    rw [ha]
    exact (canonical14113 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA849 + difference 2 1) (sourceB849 + difference 1 2) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA849 + difference 2 1) (sourceB849 + difference 1 2) sourceC849) = raw14114 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14114; decide +kernel
    rw [ha]
    exact (canonical14114 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA849 + difference 2 3) (sourceB849 + difference 3 2) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA849 + difference 2 3) (sourceB849 + difference 3 2) sourceC849) = raw14115 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14115; decide +kernel
    rw [ha]
    exact (canonical14115 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA849 + difference 2 4) (sourceB849 + difference 4 2) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA849 + difference 2 4) (sourceB849 + difference 4 2) sourceC849) = raw14116 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14116; decide +kernel
    rw [ha]
    exact (canonical14116 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA849 + difference 2 5) (sourceB849 + difference 5 2) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA849 + difference 2 5) (sourceB849 + difference 5 2) sourceC849) = raw14117 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14117; decide +kernel
    rw [ha]
    exact (canonical14117 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA849 + difference 3 0) (sourceB849 + difference 0 3) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA849 + difference 3 0) (sourceB849 + difference 0 3) sourceC849) = raw14118 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14118; decide +kernel
    rw [ha]
    exact (canonical14118 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA849 + difference 3 1) (sourceB849 + difference 1 3) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA849 + difference 3 1) (sourceB849 + difference 1 3) sourceC849) = raw14119 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14119; decide +kernel
    rw [ha]
    exact (canonical14119 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA849 + difference 3 2) (sourceB849 + difference 2 3) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA849 + difference 3 2) (sourceB849 + difference 2 3) sourceC849) = raw14120 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14120; decide +kernel
    rw [ha]
    exact (canonical14120 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA849 + difference 3 4) (sourceB849 + difference 4 3) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA849 + difference 3 4) (sourceB849 + difference 4 3) sourceC849) = raw14121 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14121; decide +kernel
    rw [ha]
    exact (canonical14121 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA849 + difference 3 5) (sourceB849 + difference 5 3) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA849 + difference 3 5) (sourceB849 + difference 5 3) sourceC849) = raw14122 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14122; decide +kernel
    rw [ha]
    exact (canonical14122 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA849 + difference 4 0) (sourceB849 + difference 0 4) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA849 + difference 4 0) (sourceB849 + difference 0 4) sourceC849) = raw14123 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14123; decide +kernel
    rw [ha]
    exact (canonical14123 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA849 + difference 4 1) (sourceB849 + difference 1 4) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA849 + difference 4 1) (sourceB849 + difference 1 4) sourceC849) = raw14124 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14124; decide +kernel
    rw [ha]
    exact (canonical14124 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA849 + difference 4 2) (sourceB849 + difference 2 4) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA849 + difference 4 2) (sourceB849 + difference 2 4) sourceC849) = raw14125 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14125; decide +kernel
    rw [ha]
    exact (canonical14125 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA849 + difference 4 3) (sourceB849 + difference 3 4) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA849 + difference 4 3) (sourceB849 + difference 3 4) sourceC849) = raw14126 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14126; decide +kernel
    rw [ha]
    exact (canonical14126 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA849 + difference 4 5) (sourceB849 + difference 5 4) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA849 + difference 4 5) (sourceB849 + difference 5 4) sourceC849) = raw14127 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14127; decide +kernel
    rw [ha]
    exact (canonical14127 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA849 + difference 5 0) (sourceB849 + difference 0 5) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA849 + difference 5 0) (sourceB849 + difference 0 5) sourceC849) = raw14128 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14128; decide +kernel
    rw [ha]
    exact (canonical14128 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA849 + difference 5 1) (sourceB849 + difference 1 5) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA849 + difference 5 1) (sourceB849 + difference 1 5) sourceC849) = raw14129 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14129; decide +kernel
    rw [ha]
    exact (canonical14129 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA849 + difference 5 2) (sourceB849 + difference 2 5) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA849 + difference 5 2) (sourceB849 + difference 2 5) sourceC849) = raw14130 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14130; decide +kernel
    rw [ha]
    exact (canonical14130 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA849 + difference 5 3) (sourceB849 + difference 3 5) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA849 + difference 5 3) (sourceB849 + difference 3 5) sourceC849) = raw14131 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14131; decide +kernel
    rw [ha]
    exact (canonical14131 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA849 + difference 5 4) (sourceB849 + difference 4 5) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA849 + difference 5 4) (sourceB849 + difference 4 5) sourceC849) = raw14132 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14132; decide +kernel
    rw [ha]
    exact (canonical14132 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA849 sourceB849 sourceC849
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm849, Integer.Sparse.eval]
  linarith only [hs]

def sourceA850 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB850 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC850 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceForm850 : Integer.Sparse Master := [(Sum.inr 4417, 1), (Sum.inr 4418, 1), (Sum.inr 4419, 1), (Sum.inr 4424, 1), (Sum.inr 4495, 1), (Sum.inr 5013, 1), (Sum.inr 5014, 1), (Sum.inr 5015, 1), (Sum.inr 5018, 1), (Sum.inr 5055, 1), (Sum.inr 5056, 1), (Sum.inr 5059, 1), (Sum.inr 5098, 1), (Sum.inr 5099, 1), (Sum.inr 5247, 1), (Sum.inr 5248, 1), (Sum.inr 5257, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5271, 2), (Sum.inr 5272, 1), (Sum.inr 5275, 1), (Sum.inr 5292, 1), (Sum.inr 5306, 1), (Sum.inr 5473, 1), (Sum.inr 5478, 1), (Sum.inr 5485, 1), (Sum.inr 5490, 1), (Sum.inr 5492, 1)]

theorem sourceEq850 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm850 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA850 + difference 0 1) (sourceB850 + difference 1 0) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA850 + difference 0 1) (sourceB850 + difference 1 0) sourceC850) = raw14133 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14133; decide +kernel
    rw [ha]
    exact (canonical14133 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA850 + difference 0 2) (sourceB850 + difference 2 0) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA850 + difference 0 2) (sourceB850 + difference 2 0) sourceC850) = raw14134 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14134; decide +kernel
    rw [ha]
    exact (canonical14134 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA850 + difference 0 3) (sourceB850 + difference 3 0) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA850 + difference 0 3) (sourceB850 + difference 3 0) sourceC850) = raw14135 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14135; decide +kernel
    rw [ha]
    exact (canonical14135 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA850 + difference 0 4) (sourceB850 + difference 4 0) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA850 + difference 0 4) (sourceB850 + difference 4 0) sourceC850) = raw14136 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14136; decide +kernel
    rw [ha]
    exact (canonical14136 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA850 + difference 0 5) (sourceB850 + difference 5 0) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA850 + difference 0 5) (sourceB850 + difference 5 0) sourceC850) = raw14137 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14137; decide +kernel
    rw [ha]
    exact (canonical14137 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA850 + difference 1 0) (sourceB850 + difference 0 1) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA850 + difference 1 0) (sourceB850 + difference 0 1) sourceC850) = raw14138 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14138; decide +kernel
    rw [ha]
    exact (canonical14138 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA850 + difference 1 2) (sourceB850 + difference 2 1) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA850 + difference 1 2) (sourceB850 + difference 2 1) sourceC850) = raw14139 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14139; decide +kernel
    rw [ha]
    exact (canonical14139 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA850 + difference 1 3) (sourceB850 + difference 3 1) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA850 + difference 1 3) (sourceB850 + difference 3 1) sourceC850) = raw14140 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14140; decide +kernel
    rw [ha]
    exact (canonical14140 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA850 + difference 1 4) (sourceB850 + difference 4 1) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA850 + difference 1 4) (sourceB850 + difference 4 1) sourceC850) = raw14141 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14141; decide +kernel
    rw [ha]
    exact (canonical14141 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA850 + difference 1 5) (sourceB850 + difference 5 1) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA850 + difference 1 5) (sourceB850 + difference 5 1) sourceC850) = raw14142 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14142; decide +kernel
    rw [ha]
    exact (canonical14142 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA850 + difference 2 0) (sourceB850 + difference 0 2) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA850 + difference 2 0) (sourceB850 + difference 0 2) sourceC850) = raw14143 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14143; decide +kernel
    rw [ha]
    exact (canonical14143 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA850 + difference 2 1) (sourceB850 + difference 1 2) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA850 + difference 2 1) (sourceB850 + difference 1 2) sourceC850) = raw14144 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14144; decide +kernel
    rw [ha]
    exact (canonical14144 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA850 + difference 2 3) (sourceB850 + difference 3 2) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA850 + difference 2 3) (sourceB850 + difference 3 2) sourceC850) = raw14145 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14145; decide +kernel
    rw [ha]
    exact (canonical14145 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA850 + difference 2 4) (sourceB850 + difference 4 2) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA850 + difference 2 4) (sourceB850 + difference 4 2) sourceC850) = raw14146 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14146; decide +kernel
    rw [ha]
    exact (canonical14146 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA850 + difference 2 5) (sourceB850 + difference 5 2) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA850 + difference 2 5) (sourceB850 + difference 5 2) sourceC850) = raw14147 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14147; decide +kernel
    rw [ha]
    exact (canonical14147 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA850 + difference 3 0) (sourceB850 + difference 0 3) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA850 + difference 3 0) (sourceB850 + difference 0 3) sourceC850) = raw14148 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14148; decide +kernel
    rw [ha]
    exact (canonical14148 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA850 + difference 3 1) (sourceB850 + difference 1 3) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA850 + difference 3 1) (sourceB850 + difference 1 3) sourceC850) = raw14149 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14149; decide +kernel
    rw [ha]
    exact (canonical14149 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA850 + difference 3 2) (sourceB850 + difference 2 3) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA850 + difference 3 2) (sourceB850 + difference 2 3) sourceC850) = raw14150 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14150; decide +kernel
    rw [ha]
    exact (canonical14150 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA850 + difference 3 4) (sourceB850 + difference 4 3) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA850 + difference 3 4) (sourceB850 + difference 4 3) sourceC850) = raw14151 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14151; decide +kernel
    rw [ha]
    exact (canonical14151 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA850 + difference 3 5) (sourceB850 + difference 5 3) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA850 + difference 3 5) (sourceB850 + difference 5 3) sourceC850) = raw14152 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14152; decide +kernel
    rw [ha]
    exact (canonical14152 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA850 + difference 4 0) (sourceB850 + difference 0 4) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA850 + difference 4 0) (sourceB850 + difference 0 4) sourceC850) = raw14153 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14153; decide +kernel
    rw [ha]
    exact (canonical14153 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA850 + difference 4 1) (sourceB850 + difference 1 4) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA850 + difference 4 1) (sourceB850 + difference 1 4) sourceC850) = raw14154 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14154; decide +kernel
    rw [ha]
    exact (canonical14154 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA850 + difference 4 2) (sourceB850 + difference 2 4) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA850 + difference 4 2) (sourceB850 + difference 2 4) sourceC850) = raw14155 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14155; decide +kernel
    rw [ha]
    exact (canonical14155 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA850 + difference 4 3) (sourceB850 + difference 3 4) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA850 + difference 4 3) (sourceB850 + difference 3 4) sourceC850) = raw14156 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14156; decide +kernel
    rw [ha]
    exact (canonical14156 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA850 + difference 4 5) (sourceB850 + difference 5 4) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA850 + difference 4 5) (sourceB850 + difference 5 4) sourceC850) = raw14157 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14157; decide +kernel
    rw [ha]
    exact (canonical14157 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA850 + difference 5 0) (sourceB850 + difference 0 5) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA850 + difference 5 0) (sourceB850 + difference 0 5) sourceC850) = raw14158 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14158; decide +kernel
    rw [ha]
    exact (canonical14158 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA850 + difference 5 1) (sourceB850 + difference 1 5) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA850 + difference 5 1) (sourceB850 + difference 1 5) sourceC850) = raw14159 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14159; decide +kernel
    rw [ha]
    exact (canonical14159 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA850 + difference 5 2) (sourceB850 + difference 2 5) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA850 + difference 5 2) (sourceB850 + difference 2 5) sourceC850) = raw14160 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14160; decide +kernel
    rw [ha]
    exact (canonical14160 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA850 + difference 5 3) (sourceB850 + difference 3 5) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA850 + difference 5 3) (sourceB850 + difference 3 5) sourceC850) = raw14161 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14161; decide +kernel
    rw [ha]
    exact (canonical14161 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA850 + difference 5 4) (sourceB850 + difference 4 5) sourceC850) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA850 + difference 5 4) (sourceB850 + difference 4 5) sourceC850) = raw14162 := by
      apply Matrix.ext; unfold tripleCharges sourceA850 sourceB850 sourceC850 difference raw14162; decide +kernel
    rw [ha]
    exact (canonical14162 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA850 sourceB850 sourceC850
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm850, Integer.Sparse.eval]
  linarith only [hs]

def sourceA851 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB851 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC851 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceForm851 : Integer.Sparse Master := [(Sum.inr 998, 1), (Sum.inr 999, 1), (Sum.inr 1000, 1), (Sum.inr 1005, 1), (Sum.inr 1079, 1), (Sum.inr 2398, 1), (Sum.inr 2399, 1), (Sum.inr 2400, 1), (Sum.inr 2404, 1), (Sum.inr 2458, 1), (Sum.inr 2459, 1), (Sum.inr 2462, 1), (Sum.inr 2508, 1), (Sum.inr 2703, 1), (Sum.inr 2704, 1), (Sum.inr 2705, 1), (Sum.inr 2721, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2739, 2), (Sum.inr 2740, 1), (Sum.inr 2743, 1), (Sum.inr 2766, 1), (Sum.inr 2784, 1), (Sum.inr 3961, 1), (Sum.inr 3974, 1), (Sum.inr 4010, 1), (Sum.inr 4013, 1), (Sum.inr 4015, 1)]

theorem sourceEq851 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm851 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA851 + difference 0 1) (sourceB851 + difference 1 0) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA851 + difference 0 1) (sourceB851 + difference 1 0) sourceC851) = raw14163 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14163; decide +kernel
    rw [ha]
    exact (canonical14163 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA851 + difference 0 2) (sourceB851 + difference 2 0) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA851 + difference 0 2) (sourceB851 + difference 2 0) sourceC851) = raw14164 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14164; decide +kernel
    rw [ha]
    exact (canonical14164 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA851 + difference 0 3) (sourceB851 + difference 3 0) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA851 + difference 0 3) (sourceB851 + difference 3 0) sourceC851) = raw14165 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14165; decide +kernel
    rw [ha]
    exact (canonical14165 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA851 + difference 0 4) (sourceB851 + difference 4 0) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4015) := by
    have ha : (tripleCharges (sourceA851 + difference 0 4) (sourceB851 + difference 4 0) sourceC851) = raw14166 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14166; decide +kernel
    rw [ha]
    exact (canonical14166 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA851 + difference 0 5) (sourceB851 + difference 5 0) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA851 + difference 0 5) (sourceB851 + difference 5 0) sourceC851) = raw14167 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14167; decide +kernel
    rw [ha]
    exact (canonical14167 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA851 + difference 1 0) (sourceB851 + difference 0 1) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA851 + difference 1 0) (sourceB851 + difference 0 1) sourceC851) = raw14168 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14168; decide +kernel
    rw [ha]
    exact (canonical14168 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA851 + difference 1 2) (sourceB851 + difference 2 1) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2398) := by
    have ha : (tripleCharges (sourceA851 + difference 1 2) (sourceB851 + difference 2 1) sourceC851) = raw14169 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14169; decide +kernel
    rw [ha]
    exact (canonical14169 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA851 + difference 1 3) (sourceB851 + difference 3 1) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA851 + difference 1 3) (sourceB851 + difference 3 1) sourceC851) = raw14170 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14170; decide +kernel
    rw [ha]
    exact (canonical14170 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA851 + difference 1 4) (sourceB851 + difference 4 1) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA851 + difference 1 4) (sourceB851 + difference 4 1) sourceC851) = raw14171 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14171; decide +kernel
    rw [ha]
    exact (canonical14171 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA851 + difference 1 5) (sourceB851 + difference 5 1) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA851 + difference 1 5) (sourceB851 + difference 5 1) sourceC851) = raw14172 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14172; decide +kernel
    rw [ha]
    exact (canonical14172 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA851 + difference 2 0) (sourceB851 + difference 0 2) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA851 + difference 2 0) (sourceB851 + difference 0 2) sourceC851) = raw14173 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14173; decide +kernel
    rw [ha]
    exact (canonical14173 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA851 + difference 2 1) (sourceB851 + difference 1 2) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA851 + difference 2 1) (sourceB851 + difference 1 2) sourceC851) = raw14174 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14174; decide +kernel
    rw [ha]
    exact (canonical14174 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA851 + difference 2 3) (sourceB851 + difference 3 2) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA851 + difference 2 3) (sourceB851 + difference 3 2) sourceC851) = raw14175 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14175; decide +kernel
    rw [ha]
    exact (canonical14175 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA851 + difference 2 4) (sourceB851 + difference 4 2) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA851 + difference 2 4) (sourceB851 + difference 4 2) sourceC851) = raw14176 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14176; decide +kernel
    rw [ha]
    exact (canonical14176 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA851 + difference 2 5) (sourceB851 + difference 5 2) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA851 + difference 2 5) (sourceB851 + difference 5 2) sourceC851) = raw14177 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14177; decide +kernel
    rw [ha]
    exact (canonical14177 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA851 + difference 3 0) (sourceB851 + difference 0 3) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA851 + difference 3 0) (sourceB851 + difference 0 3) sourceC851) = raw14178 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14178; decide +kernel
    rw [ha]
    exact (canonical14178 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA851 + difference 3 1) (sourceB851 + difference 1 3) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2458) := by
    have ha : (tripleCharges (sourceA851 + difference 3 1) (sourceB851 + difference 1 3) sourceC851) = raw14179 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14179; decide +kernel
    rw [ha]
    exact (canonical14179 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA851 + difference 3 2) (sourceB851 + difference 2 3) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2399) := by
    have ha : (tripleCharges (sourceA851 + difference 3 2) (sourceB851 + difference 2 3) sourceC851) = raw14180 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14180; decide +kernel
    rw [ha]
    exact (canonical14180 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA851 + difference 3 4) (sourceB851 + difference 4 3) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA851 + difference 3 4) (sourceB851 + difference 4 3) sourceC851) = raw14181 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14181; decide +kernel
    rw [ha]
    exact (canonical14181 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA851 + difference 3 5) (sourceB851 + difference 5 3) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA851 + difference 3 5) (sourceB851 + difference 5 3) sourceC851) = raw14182 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14182; decide +kernel
    rw [ha]
    exact (canonical14182 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA851 + difference 4 0) (sourceB851 + difference 0 4) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA851 + difference 4 0) (sourceB851 + difference 0 4) sourceC851) = raw14183 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14183; decide +kernel
    rw [ha]
    exact (canonical14183 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA851 + difference 4 1) (sourceB851 + difference 1 4) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA851 + difference 4 1) (sourceB851 + difference 1 4) sourceC851) = raw14184 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14184; decide +kernel
    rw [ha]
    exact (canonical14184 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA851 + difference 4 2) (sourceB851 + difference 2 4) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2400) := by
    have ha : (tripleCharges (sourceA851 + difference 4 2) (sourceB851 + difference 2 4) sourceC851) = raw14185 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14185; decide +kernel
    rw [ha]
    exact (canonical14185 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA851 + difference 4 3) (sourceB851 + difference 3 4) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA851 + difference 4 3) (sourceB851 + difference 3 4) sourceC851) = raw14186 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14186; decide +kernel
    rw [ha]
    exact (canonical14186 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA851 + difference 4 5) (sourceB851 + difference 5 4) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA851 + difference 4 5) (sourceB851 + difference 5 4) sourceC851) = raw14187 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14187; decide +kernel
    rw [ha]
    exact (canonical14187 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA851 + difference 5 0) (sourceB851 + difference 0 5) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA851 + difference 5 0) (sourceB851 + difference 0 5) sourceC851) = raw14188 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14188; decide +kernel
    rw [ha]
    exact (canonical14188 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA851 + difference 5 1) (sourceB851 + difference 1 5) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA851 + difference 5 1) (sourceB851 + difference 1 5) sourceC851) = raw14189 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14189; decide +kernel
    rw [ha]
    exact (canonical14189 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA851 + difference 5 2) (sourceB851 + difference 2 5) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2404) := by
    have ha : (tripleCharges (sourceA851 + difference 5 2) (sourceB851 + difference 2 5) sourceC851) = raw14190 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14190; decide +kernel
    rw [ha]
    exact (canonical14190 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA851 + difference 5 3) (sourceB851 + difference 3 5) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA851 + difference 5 3) (sourceB851 + difference 3 5) sourceC851) = raw14191 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14191; decide +kernel
    rw [ha]
    exact (canonical14191 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA851 + difference 5 4) (sourceB851 + difference 4 5) sourceC851) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA851 + difference 5 4) (sourceB851 + difference 4 5) sourceC851) = raw14192 := by
      apply Matrix.ext; unfold tripleCharges sourceA851 sourceB851 sourceC851 difference raw14192; decide +kernel
    rw [ha]
    exact (canonical14192 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA851 sourceB851 sourceC851
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm851, Integer.Sparse.eval]
  linarith only [hs]

def sourceA852 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceB852 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC852 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm852 : Integer.Sparse Master := [(Sum.inr 4802, 1), (Sum.inr 4807, 1), (Sum.inr 4811, 1), (Sum.inr 4838, 1), (Sum.inr 4895, 1), (Sum.inr 5150, 1), (Sum.inr 5151, 1), (Sum.inr 5173, 1), (Sum.inr 5226, 1), (Sum.inr 5236, 1), (Sum.inr 5237, 1), (Sum.inr 5246, 1), (Sum.inr 5247, 1), (Sum.inr 5255, 1), (Sum.inr 5256, 1), (Sum.inr 5257, 1), (Sum.inr 5269, 1), (Sum.inr 5270, 1), (Sum.inr 5271, 3), (Sum.inr 5273, 1), (Sum.inr 5281, 1), (Sum.inr 5289, 1), (Sum.inr 5290, 1), (Sum.inr 5292, 1), (Sum.inr 5299, 1), (Sum.inr 5304, 1), (Sum.inr 5306, 1), (Sum.inr 5307, 1)]

theorem sourceEq852 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm852 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA852 + difference 0 1) (sourceB852 + difference 1 0) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA852 + difference 0 1) (sourceB852 + difference 1 0) sourceC852) = raw14193 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14193; decide +kernel
    rw [ha]
    exact (canonical14193 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA852 + difference 0 2) (sourceB852 + difference 2 0) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA852 + difference 0 2) (sourceB852 + difference 2 0) sourceC852) = raw14194 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14194; decide +kernel
    rw [ha]
    exact (canonical14194 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA852 + difference 0 3) (sourceB852 + difference 3 0) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA852 + difference 0 3) (sourceB852 + difference 3 0) sourceC852) = raw13835 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw13835; decide +kernel
    rw [ha]
    exact (canonical13835 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA852 + difference 0 4) (sourceB852 + difference 4 0) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA852 + difference 0 4) (sourceB852 + difference 4 0) sourceC852) = raw14195 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14195; decide +kernel
    rw [ha]
    exact (canonical14195 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA852 + difference 0 5) (sourceB852 + difference 5 0) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA852 + difference 0 5) (sourceB852 + difference 5 0) sourceC852) = raw14014 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14014; decide +kernel
    rw [ha]
    exact (canonical14014 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA852 + difference 1 0) (sourceB852 + difference 0 1) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA852 + difference 1 0) (sourceB852 + difference 0 1) sourceC852) = raw13844 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw13844; decide +kernel
    rw [ha]
    exact (canonical13844 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA852 + difference 1 2) (sourceB852 + difference 2 1) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA852 + difference 1 2) (sourceB852 + difference 2 1) sourceC852) = raw13846 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw13846; decide +kernel
    rw [ha]
    exact (canonical13846 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA852 + difference 1 3) (sourceB852 + difference 3 1) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA852 + difference 1 3) (sourceB852 + difference 3 1) sourceC852) = raw13642 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw13642; decide +kernel
    rw [ha]
    exact (canonical13642 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA852 + difference 1 4) (sourceB852 + difference 4 1) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA852 + difference 1 4) (sourceB852 + difference 4 1) sourceC852) = raw13847 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw13847; decide +kernel
    rw [ha]
    exact (canonical13847 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA852 + difference 1 5) (sourceB852 + difference 5 1) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA852 + difference 1 5) (sourceB852 + difference 5 1) sourceC852) = raw13632 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw13632; decide +kernel
    rw [ha]
    exact (canonical13632 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA852 + difference 2 0) (sourceB852 + difference 0 2) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA852 + difference 2 0) (sourceB852 + difference 0 2) sourceC852) = raw14030 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14030; decide +kernel
    rw [ha]
    exact (canonical14030 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA852 + difference 2 1) (sourceB852 + difference 1 2) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA852 + difference 2 1) (sourceB852 + difference 1 2) sourceC852) = raw14031 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14031; decide +kernel
    rw [ha]
    exact (canonical14031 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA852 + difference 2 3) (sourceB852 + difference 3 2) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA852 + difference 2 3) (sourceB852 + difference 3 2) sourceC852) = raw13641 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw13641; decide +kernel
    rw [ha]
    exact (canonical13641 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA852 + difference 2 4) (sourceB852 + difference 4 2) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA852 + difference 2 4) (sourceB852 + difference 4 2) sourceC852) = raw14032 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14032; decide +kernel
    rw [ha]
    exact (canonical14032 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA852 + difference 2 5) (sourceB852 + difference 5 2) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA852 + difference 2 5) (sourceB852 + difference 5 2) sourceC852) = raw13631 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw13631; decide +kernel
    rw [ha]
    exact (canonical13631 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA852 + difference 3 0) (sourceB852 + difference 0 3) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA852 + difference 3 0) (sourceB852 + difference 0 3) sourceC852) = raw14196 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14196; decide +kernel
    rw [ha]
    exact (canonical14196 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA852 + difference 3 1) (sourceB852 + difference 1 3) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA852 + difference 3 1) (sourceB852 + difference 1 3) sourceC852) = raw14197 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14197; decide +kernel
    rw [ha]
    exact (canonical14197 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA852 + difference 3 2) (sourceB852 + difference 2 3) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA852 + difference 3 2) (sourceB852 + difference 2 3) sourceC852) = raw14198 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14198; decide +kernel
    rw [ha]
    exact (canonical14198 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA852 + difference 3 4) (sourceB852 + difference 4 3) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA852 + difference 3 4) (sourceB852 + difference 4 3) sourceC852) = raw14199 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14199; decide +kernel
    rw [ha]
    exact (canonical14199 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA852 + difference 3 5) (sourceB852 + difference 5 3) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA852 + difference 3 5) (sourceB852 + difference 5 3) sourceC852) = raw14023 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14023; decide +kernel
    rw [ha]
    exact (canonical14023 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA852 + difference 4 0) (sourceB852 + difference 0 4) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA852 + difference 4 0) (sourceB852 + difference 0 4) sourceC852) = raw14200 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14200; decide +kernel
    rw [ha]
    exact (canonical14200 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA852 + difference 4 1) (sourceB852 + difference 1 4) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5246) := by
    have ha : (tripleCharges (sourceA852 + difference 4 1) (sourceB852 + difference 1 4) sourceC852) = raw14201 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14201; decide +kernel
    rw [ha]
    exact (canonical14201 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA852 + difference 4 2) (sourceB852 + difference 2 4) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA852 + difference 4 2) (sourceB852 + difference 2 4) sourceC852) = raw14202 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14202; decide +kernel
    rw [ha]
    exact (canonical14202 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA852 + difference 4 3) (sourceB852 + difference 3 4) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA852 + difference 4 3) (sourceB852 + difference 3 4) sourceC852) = raw13849 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw13849; decide +kernel
    rw [ha]
    exact (canonical13849 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA852 + difference 4 5) (sourceB852 + difference 5 4) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA852 + difference 4 5) (sourceB852 + difference 5 4) sourceC852) = raw14028 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14028; decide +kernel
    rw [ha]
    exact (canonical14028 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA852 + difference 5 0) (sourceB852 + difference 0 5) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA852 + difference 5 0) (sourceB852 + difference 0 5) sourceC852) = raw14203 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14203; decide +kernel
    rw [ha]
    exact (canonical14203 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA852 + difference 5 1) (sourceB852 + difference 1 5) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA852 + difference 5 1) (sourceB852 + difference 1 5) sourceC852) = raw14204 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14204; decide +kernel
    rw [ha]
    exact (canonical14204 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA852 + difference 5 2) (sourceB852 + difference 2 5) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA852 + difference 5 2) (sourceB852 + difference 2 5) sourceC852) = raw14205 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14205; decide +kernel
    rw [ha]
    exact (canonical14205 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA852 + difference 5 3) (sourceB852 + difference 3 5) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA852 + difference 5 3) (sourceB852 + difference 3 5) sourceC852) = raw13853 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw13853; decide +kernel
    rw [ha]
    exact (canonical13853 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA852 + difference 5 4) (sourceB852 + difference 4 5) sourceC852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA852 + difference 5 4) (sourceB852 + difference 4 5) sourceC852) = raw14206 := by
      apply Matrix.ext; unfold tripleCharges sourceA852 sourceB852 sourceC852 difference raw14206; decide +kernel
    rw [ha]
    exact (canonical14206 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA852 sourceB852 sourceC852
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm852, Integer.Sparse.eval]
  linarith only [hs]

def sourceA853 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceB853 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC853 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm853 : Integer.Sparse Master := [(Sum.inr 2202, 1), (Sum.inr 2224, 1), (Sum.inr 2225, 1), (Sum.inr 2227, 1), (Sum.inr 2291, 1), (Sum.inr 2669, 1), (Sum.inr 2681, 1), (Sum.inr 2682, 1), (Sum.inr 2684, 1), (Sum.inr 2700, 1), (Sum.inr 2701, 1), (Sum.inr 2703, 1), (Sum.inr 2718, 1), (Sum.inr 2720, 1), (Sum.inr 2721, 1), (Sum.inr 2735, 1), (Sum.inr 2736, 1), (Sum.inr 2738, 1), (Sum.inr 2739, 3), (Sum.inr 2741, 1), (Sum.inr 2782, 1), (Sum.inr 2784, 1), (Sum.inr 2785, 1), (Sum.inr 3051, 1), (Sum.inr 3074, 1), (Sum.inr 3097, 1), (Sum.inr 3099, 1), (Sum.inr 3100, 1)]

theorem sourceEq853 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm853 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA853 + difference 0 1) (sourceB853 + difference 1 0) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA853 + difference 0 1) (sourceB853 + difference 1 0) sourceC853) = raw14207 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14207; decide +kernel
    rw [ha]
    exact (canonical14207 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA853 + difference 0 2) (sourceB853 + difference 2 0) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA853 + difference 0 2) (sourceB853 + difference 2 0) sourceC853) = raw14208 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14208; decide +kernel
    rw [ha]
    exact (canonical14208 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA853 + difference 0 3) (sourceB853 + difference 3 0) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA853 + difference 0 3) (sourceB853 + difference 3 0) sourceC853) = raw13857 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw13857; decide +kernel
    rw [ha]
    exact (canonical13857 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA853 + difference 0 4) (sourceB853 + difference 4 0) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA853 + difference 0 4) (sourceB853 + difference 4 0) sourceC853) = raw14209 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14209; decide +kernel
    rw [ha]
    exact (canonical14209 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA853 + difference 0 5) (sourceB853 + difference 5 0) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA853 + difference 0 5) (sourceB853 + difference 5 0) sourceC853) = raw14034 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14034; decide +kernel
    rw [ha]
    exact (canonical14034 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA853 + difference 1 0) (sourceB853 + difference 0 1) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA853 + difference 1 0) (sourceB853 + difference 0 1) sourceC853) = raw13866 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw13866; decide +kernel
    rw [ha]
    exact (canonical13866 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA853 + difference 1 2) (sourceB853 + difference 2 1) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA853 + difference 1 2) (sourceB853 + difference 2 1) sourceC853) = raw13868 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw13868; decide +kernel
    rw [ha]
    exact (canonical13868 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA853 + difference 1 3) (sourceB853 + difference 3 1) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA853 + difference 1 3) (sourceB853 + difference 3 1) sourceC853) = raw13670 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw13670; decide +kernel
    rw [ha]
    exact (canonical13670 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA853 + difference 1 4) (sourceB853 + difference 4 1) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA853 + difference 1 4) (sourceB853 + difference 4 1) sourceC853) = raw13869 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw13869; decide +kernel
    rw [ha]
    exact (canonical13869 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA853 + difference 1 5) (sourceB853 + difference 5 1) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA853 + difference 1 5) (sourceB853 + difference 5 1) sourceC853) = raw13660 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw13660; decide +kernel
    rw [ha]
    exact (canonical13660 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA853 + difference 2 0) (sourceB853 + difference 0 2) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA853 + difference 2 0) (sourceB853 + difference 0 2) sourceC853) = raw14050 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14050; decide +kernel
    rw [ha]
    exact (canonical14050 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA853 + difference 2 1) (sourceB853 + difference 1 2) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA853 + difference 2 1) (sourceB853 + difference 1 2) sourceC853) = raw14051 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14051; decide +kernel
    rw [ha]
    exact (canonical14051 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA853 + difference 2 3) (sourceB853 + difference 3 2) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2785) := by
    have ha : (tripleCharges (sourceA853 + difference 2 3) (sourceB853 + difference 3 2) sourceC853) = raw13669 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw13669; decide +kernel
    rw [ha]
    exact (canonical13669 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA853 + difference 2 4) (sourceB853 + difference 4 2) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA853 + difference 2 4) (sourceB853 + difference 4 2) sourceC853) = raw14052 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14052; decide +kernel
    rw [ha]
    exact (canonical14052 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA853 + difference 2 5) (sourceB853 + difference 5 2) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA853 + difference 2 5) (sourceB853 + difference 5 2) sourceC853) = raw13659 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw13659; decide +kernel
    rw [ha]
    exact (canonical13659 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA853 + difference 3 0) (sourceB853 + difference 0 3) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA853 + difference 3 0) (sourceB853 + difference 0 3) sourceC853) = raw14210 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14210; decide +kernel
    rw [ha]
    exact (canonical14210 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA853 + difference 3 1) (sourceB853 + difference 1 3) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA853 + difference 3 1) (sourceB853 + difference 1 3) sourceC853) = raw14211 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14211; decide +kernel
    rw [ha]
    exact (canonical14211 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA853 + difference 3 2) (sourceB853 + difference 2 3) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA853 + difference 3 2) (sourceB853 + difference 2 3) sourceC853) = raw14212 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14212; decide +kernel
    rw [ha]
    exact (canonical14212 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA853 + difference 3 4) (sourceB853 + difference 4 3) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA853 + difference 3 4) (sourceB853 + difference 4 3) sourceC853) = raw14213 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14213; decide +kernel
    rw [ha]
    exact (canonical14213 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA853 + difference 3 5) (sourceB853 + difference 5 3) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA853 + difference 3 5) (sourceB853 + difference 5 3) sourceC853) = raw14043 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14043; decide +kernel
    rw [ha]
    exact (canonical14043 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA853 + difference 4 0) (sourceB853 + difference 0 4) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA853 + difference 4 0) (sourceB853 + difference 0 4) sourceC853) = raw14214 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14214; decide +kernel
    rw [ha]
    exact (canonical14214 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA853 + difference 4 1) (sourceB853 + difference 1 4) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2701) := by
    have ha : (tripleCharges (sourceA853 + difference 4 1) (sourceB853 + difference 1 4) sourceC853) = raw14215 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14215; decide +kernel
    rw [ha]
    exact (canonical14215 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA853 + difference 4 2) (sourceB853 + difference 2 4) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA853 + difference 4 2) (sourceB853 + difference 2 4) sourceC853) = raw14216 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14216; decide +kernel
    rw [ha]
    exact (canonical14216 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA853 + difference 4 3) (sourceB853 + difference 3 4) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA853 + difference 4 3) (sourceB853 + difference 3 4) sourceC853) = raw13871 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw13871; decide +kernel
    rw [ha]
    exact (canonical13871 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA853 + difference 4 5) (sourceB853 + difference 5 4) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA853 + difference 4 5) (sourceB853 + difference 5 4) sourceC853) = raw14048 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14048; decide +kernel
    rw [ha]
    exact (canonical14048 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA853 + difference 5 0) (sourceB853 + difference 0 5) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA853 + difference 5 0) (sourceB853 + difference 0 5) sourceC853) = raw14217 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14217; decide +kernel
    rw [ha]
    exact (canonical14217 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA853 + difference 5 1) (sourceB853 + difference 1 5) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA853 + difference 5 1) (sourceB853 + difference 1 5) sourceC853) = raw14218 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14218; decide +kernel
    rw [ha]
    exact (canonical14218 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA853 + difference 5 2) (sourceB853 + difference 2 5) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA853 + difference 5 2) (sourceB853 + difference 2 5) sourceC853) = raw14219 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14219; decide +kernel
    rw [ha]
    exact (canonical14219 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA853 + difference 5 3) (sourceB853 + difference 3 5) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA853 + difference 5 3) (sourceB853 + difference 3 5) sourceC853) = raw13875 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw13875; decide +kernel
    rw [ha]
    exact (canonical13875 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA853 + difference 5 4) (sourceB853 + difference 4 5) sourceC853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA853 + difference 5 4) (sourceB853 + difference 4 5) sourceC853) = raw14220 := by
      apply Matrix.ext; unfold tripleCharges sourceA853 sourceB853 sourceC853 difference raw14220; decide +kernel
    rw [ha]
    exact (canonical14220 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA853 sourceB853 sourceC853
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm853, Integer.Sparse.eval]
  linarith only [hs]

def sourceA854 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB854 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceC854 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm854 : Integer.Sparse Master := [(Sum.inr 4091, 1), (Sum.inr 4601, 1), (Sum.inr 4606, 3), (Sum.inr 4618, 1), (Sum.inr 5100, 1), (Sum.inr 5104, 3), (Sum.inr 5137, 3), (Sum.inr 5162, 1), (Sum.inr 5257, 3), (Sum.inr 5259, 6), (Sum.inr 5290, 3), (Sum.inr 5427, 1), (Sum.inr 5440, 3)]

theorem sourceEq854 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm854 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA854 + difference 0 1) (sourceB854 + difference 1 0) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA854 + difference 0 1) (sourceB854 + difference 1 0) sourceC854) = raw14221 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14221; decide +kernel
    rw [ha]
    exact (canonical14221 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA854 + difference 0 2) (sourceB854 + difference 2 0) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA854 + difference 0 2) (sourceB854 + difference 2 0) sourceC854) = raw14222 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14222; decide +kernel
    rw [ha]
    exact (canonical14222 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA854 + difference 0 3) (sourceB854 + difference 3 0) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA854 + difference 0 3) (sourceB854 + difference 3 0) sourceC854) = raw14223 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14223; decide +kernel
    rw [ha]
    exact (canonical14223 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA854 + difference 0 4) (sourceB854 + difference 4 0) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA854 + difference 0 4) (sourceB854 + difference 4 0) sourceC854) = raw14224 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14224; decide +kernel
    rw [ha]
    exact (canonical14224 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA854 + difference 0 5) (sourceB854 + difference 5 0) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA854 + difference 0 5) (sourceB854 + difference 5 0) sourceC854) = raw14225 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14225; decide +kernel
    rw [ha]
    exact (canonical14225 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA854 + difference 1 0) (sourceB854 + difference 0 1) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA854 + difference 1 0) (sourceB854 + difference 0 1) sourceC854) = raw14226 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14226; decide +kernel
    rw [ha]
    exact (canonical14226 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA854 + difference 1 2) (sourceB854 + difference 2 1) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5100) := by
    have ha : (tripleCharges (sourceA854 + difference 1 2) (sourceB854 + difference 2 1) sourceC854) = raw14227 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14227; decide +kernel
    rw [ha]
    exact (canonical14227 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA854 + difference 1 3) (sourceB854 + difference 3 1) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA854 + difference 1 3) (sourceB854 + difference 3 1) sourceC854) = raw14228 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14228; decide +kernel
    rw [ha]
    exact (canonical14228 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA854 + difference 1 4) (sourceB854 + difference 4 1) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA854 + difference 1 4) (sourceB854 + difference 4 1) sourceC854) = raw14229 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14229; decide +kernel
    rw [ha]
    exact (canonical14229 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA854 + difference 1 5) (sourceB854 + difference 5 1) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA854 + difference 1 5) (sourceB854 + difference 5 1) sourceC854) = raw14230 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14230; decide +kernel
    rw [ha]
    exact (canonical14230 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA854 + difference 2 0) (sourceB854 + difference 0 2) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA854 + difference 2 0) (sourceB854 + difference 0 2) sourceC854) = raw14231 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14231; decide +kernel
    rw [ha]
    exact (canonical14231 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA854 + difference 2 1) (sourceB854 + difference 1 2) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA854 + difference 2 1) (sourceB854 + difference 1 2) sourceC854) = raw14232 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14232; decide +kernel
    rw [ha]
    exact (canonical14232 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA854 + difference 2 3) (sourceB854 + difference 3 2) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA854 + difference 2 3) (sourceB854 + difference 3 2) sourceC854) = raw14233 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14233; decide +kernel
    rw [ha]
    exact (canonical14233 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA854 + difference 2 4) (sourceB854 + difference 4 2) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA854 + difference 2 4) (sourceB854 + difference 4 2) sourceC854) = raw14234 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14234; decide +kernel
    rw [ha]
    exact (canonical14234 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA854 + difference 2 5) (sourceB854 + difference 5 2) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA854 + difference 2 5) (sourceB854 + difference 5 2) sourceC854) = raw14235 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14235; decide +kernel
    rw [ha]
    exact (canonical14235 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA854 + difference 3 0) (sourceB854 + difference 0 3) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA854 + difference 3 0) (sourceB854 + difference 0 3) sourceC854) = raw14236 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14236; decide +kernel
    rw [ha]
    exact (canonical14236 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA854 + difference 3 1) (sourceB854 + difference 1 3) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA854 + difference 3 1) (sourceB854 + difference 1 3) sourceC854) = raw14237 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14237; decide +kernel
    rw [ha]
    exact (canonical14237 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA854 + difference 3 2) (sourceB854 + difference 2 3) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA854 + difference 3 2) (sourceB854 + difference 2 3) sourceC854) = raw14238 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14238; decide +kernel
    rw [ha]
    exact (canonical14238 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA854 + difference 3 4) (sourceB854 + difference 4 3) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 3 4) (sourceB854 + difference 4 3) sourceC854) = raw14239 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14239; decide +kernel
    rw [ha]
    exact (canonical14239 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA854 + difference 3 5) (sourceB854 + difference 5 3) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 3 5) (sourceB854 + difference 5 3) sourceC854) = raw14240 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14240; decide +kernel
    rw [ha]
    exact (canonical14240 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA854 + difference 4 0) (sourceB854 + difference 0 4) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA854 + difference 4 0) (sourceB854 + difference 0 4) sourceC854) = raw14241 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14241; decide +kernel
    rw [ha]
    exact (canonical14241 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA854 + difference 4 1) (sourceB854 + difference 1 4) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA854 + difference 4 1) (sourceB854 + difference 1 4) sourceC854) = raw14242 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14242; decide +kernel
    rw [ha]
    exact (canonical14242 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA854 + difference 4 2) (sourceB854 + difference 2 4) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA854 + difference 4 2) (sourceB854 + difference 2 4) sourceC854) = raw14243 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14243; decide +kernel
    rw [ha]
    exact (canonical14243 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA854 + difference 4 3) (sourceB854 + difference 3 4) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 4 3) (sourceB854 + difference 3 4) sourceC854) = raw14244 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14244; decide +kernel
    rw [ha]
    exact (canonical14244 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA854 + difference 4 5) (sourceB854 + difference 5 4) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 4 5) (sourceB854 + difference 5 4) sourceC854) = raw14245 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14245; decide +kernel
    rw [ha]
    exact (canonical14245 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA854 + difference 5 0) (sourceB854 + difference 0 5) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA854 + difference 5 0) (sourceB854 + difference 0 5) sourceC854) = raw14246 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14246; decide +kernel
    rw [ha]
    exact (canonical14246 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA854 + difference 5 1) (sourceB854 + difference 1 5) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA854 + difference 5 1) (sourceB854 + difference 1 5) sourceC854) = raw14247 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14247; decide +kernel
    rw [ha]
    exact (canonical14247 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA854 + difference 5 2) (sourceB854 + difference 2 5) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA854 + difference 5 2) (sourceB854 + difference 2 5) sourceC854) = raw14248 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14248; decide +kernel
    rw [ha]
    exact (canonical14248 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA854 + difference 5 3) (sourceB854 + difference 3 5) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 5 3) (sourceB854 + difference 3 5) sourceC854) = raw14249 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14249; decide +kernel
    rw [ha]
    exact (canonical14249 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA854 + difference 5 4) (sourceB854 + difference 4 5) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 5 4) (sourceB854 + difference 4 5) sourceC854) = raw14250 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14250; decide +kernel
    rw [ha]
    exact (canonical14250 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA854 sourceB854 sourceC854
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm854, Integer.Sparse.eval]
  linarith only [hs]

def sourceA855 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceB855 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC855 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm855 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4833, 1), (Sum.inr 4838, 3), (Sum.inr 5227, 1), (Sum.inr 5237, 3), (Sum.inr 5247, 3), (Sum.inr 5257, 3), (Sum.inr 5271, 6), (Sum.inr 5273, 1), (Sum.inr 5283, 1), (Sum.inr 5292, 3), (Sum.inr 5301, 1), (Sum.inr 5307, 3)]

theorem sourceEq855 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm855 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA855 + difference 0 1) (sourceB855 + difference 1 0) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA855 + difference 0 1) (sourceB855 + difference 1 0) sourceC855) = raw14251 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14251; decide +kernel
    rw [ha]
    exact (canonical14251 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA855 + difference 0 2) (sourceB855 + difference 2 0) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA855 + difference 0 2) (sourceB855 + difference 2 0) sourceC855) = raw14252 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14252; decide +kernel
    rw [ha]
    exact (canonical14252 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA855 + difference 0 3) (sourceB855 + difference 3 0) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA855 + difference 0 3) (sourceB855 + difference 3 0) sourceC855) = raw14253 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14253; decide +kernel
    rw [ha]
    exact (canonical14253 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA855 + difference 0 4) (sourceB855 + difference 4 0) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA855 + difference 0 4) (sourceB855 + difference 4 0) sourceC855) = raw14254 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14254; decide +kernel
    rw [ha]
    exact (canonical14254 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA855 + difference 0 5) (sourceB855 + difference 5 0) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA855 + difference 0 5) (sourceB855 + difference 5 0) sourceC855) = raw13835 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13835; decide +kernel
    rw [ha]
    exact (canonical13835 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA855 + difference 1 0) (sourceB855 + difference 0 1) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA855 + difference 1 0) (sourceB855 + difference 0 1) sourceC855) = raw13852 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13852; decide +kernel
    rw [ha]
    exact (canonical13852 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA855 + difference 1 2) (sourceB855 + difference 2 1) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA855 + difference 1 2) (sourceB855 + difference 2 1) sourceC855) = raw13854 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13854; decide +kernel
    rw [ha]
    exact (canonical13854 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA855 + difference 1 3) (sourceB855 + difference 3 1) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA855 + difference 1 3) (sourceB855 + difference 3 1) sourceC855) = raw13855 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13855; decide +kernel
    rw [ha]
    exact (canonical13855 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA855 + difference 1 4) (sourceB855 + difference 4 1) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA855 + difference 1 4) (sourceB855 + difference 4 1) sourceC855) = raw13856 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13856; decide +kernel
    rw [ha]
    exact (canonical13856 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA855 + difference 1 5) (sourceB855 + difference 5 1) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA855 + difference 1 5) (sourceB855 + difference 5 1) sourceC855) = raw13642 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13642; decide +kernel
    rw [ha]
    exact (canonical13642 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA855 + difference 2 0) (sourceB855 + difference 0 2) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA855 + difference 2 0) (sourceB855 + difference 0 2) sourceC855) = raw14255 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14255; decide +kernel
    rw [ha]
    exact (canonical14255 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA855 + difference 2 1) (sourceB855 + difference 1 2) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA855 + difference 2 1) (sourceB855 + difference 1 2) sourceC855) = raw14256 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14256; decide +kernel
    rw [ha]
    exact (canonical14256 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA855 + difference 2 3) (sourceB855 + difference 3 2) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA855 + difference 2 3) (sourceB855 + difference 3 2) sourceC855) = raw12199 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw12199; decide +kernel
    rw [ha]
    exact (canonical12199 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA855 + difference 2 4) (sourceB855 + difference 4 2) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA855 + difference 2 4) (sourceB855 + difference 4 2) sourceC855) = raw12195 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw12195; decide +kernel
    rw [ha]
    exact (canonical12195 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA855 + difference 2 5) (sourceB855 + difference 5 2) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA855 + difference 2 5) (sourceB855 + difference 5 2) sourceC855) = raw13641 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13641; decide +kernel
    rw [ha]
    exact (canonical13641 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA855 + difference 3 0) (sourceB855 + difference 0 3) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA855 + difference 3 0) (sourceB855 + difference 0 3) sourceC855) = raw14203 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14203; decide +kernel
    rw [ha]
    exact (canonical14203 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA855 + difference 3 1) (sourceB855 + difference 1 3) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA855 + difference 3 1) (sourceB855 + difference 1 3) sourceC855) = raw14204 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14204; decide +kernel
    rw [ha]
    exact (canonical14204 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA855 + difference 3 2) (sourceB855 + difference 2 3) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA855 + difference 3 2) (sourceB855 + difference 2 3) sourceC855) = raw14205 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14205; decide +kernel
    rw [ha]
    exact (canonical14205 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA855 + difference 3 4) (sourceB855 + difference 4 3) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 3 4) (sourceB855 + difference 4 3) sourceC855) = raw14206 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14206; decide +kernel
    rw [ha]
    exact (canonical14206 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA855 + difference 3 5) (sourceB855 + difference 5 3) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 3 5) (sourceB855 + difference 5 3) sourceC855) = raw13845 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13845; decide +kernel
    rw [ha]
    exact (canonical13845 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA855 + difference 4 0) (sourceB855 + difference 0 4) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA855 + difference 4 0) (sourceB855 + difference 0 4) sourceC855) = raw14257 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14257; decide +kernel
    rw [ha]
    exact (canonical14257 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA855 + difference 4 1) (sourceB855 + difference 1 4) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA855 + difference 4 1) (sourceB855 + difference 1 4) sourceC855) = raw14258 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14258; decide +kernel
    rw [ha]
    exact (canonical14258 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA855 + difference 4 2) (sourceB855 + difference 2 4) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA855 + difference 4 2) (sourceB855 + difference 2 4) sourceC855) = raw14259 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14259; decide +kernel
    rw [ha]
    exact (canonical14259 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA855 + difference 4 3) (sourceB855 + difference 3 4) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 4 3) (sourceB855 + difference 3 4) sourceC855) = raw14260 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14260; decide +kernel
    rw [ha]
    exact (canonical14260 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA855 + difference 4 5) (sourceB855 + difference 5 4) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 4 5) (sourceB855 + difference 5 4) sourceC855) = raw13849 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13849; decide +kernel
    rw [ha]
    exact (canonical13849 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA855 + difference 5 0) (sourceB855 + difference 0 5) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA855 + difference 5 0) (sourceB855 + difference 0 5) sourceC855) = raw14261 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14261; decide +kernel
    rw [ha]
    exact (canonical14261 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA855 + difference 5 1) (sourceB855 + difference 1 5) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA855 + difference 5 1) (sourceB855 + difference 1 5) sourceC855) = raw14262 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14262; decide +kernel
    rw [ha]
    exact (canonical14262 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA855 + difference 5 2) (sourceB855 + difference 2 5) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA855 + difference 5 2) (sourceB855 + difference 2 5) sourceC855) = raw14263 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14263; decide +kernel
    rw [ha]
    exact (canonical14263 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA855 + difference 5 3) (sourceB855 + difference 3 5) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 5 3) (sourceB855 + difference 3 5) sourceC855) = raw12197 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw12197; decide +kernel
    rw [ha]
    exact (canonical12197 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA855 + difference 5 4) (sourceB855 + difference 4 5) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 5 4) (sourceB855 + difference 4 5) sourceC855) = raw12193 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw12193; decide +kernel
    rw [ha]
    exact (canonical12193 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA855 sourceB855 sourceC855
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm855, Integer.Sparse.eval]
  linarith only [hs]

def sourceA856 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB856 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC856 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm856 : Integer.Sparse Master := [(Sum.inr 4438, 1), (Sum.inr 4439, 2), (Sum.inr 4456, 2), (Sum.inr 4851, 2), (Sum.inr 4852, 4), (Sum.inr 4864, 2), (Sum.inr 4885, 2), (Sum.inr 4887, 2), (Sum.inr 4888, 2), (Sum.inr 4889, 2), (Sum.inr 4893, 4), (Sum.inr 5281, 2), (Sum.inr 5283, 1), (Sum.inr 5292, 2)]

theorem sourceEq856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm856 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA856 + difference 0 1) (sourceB856 + difference 1 0) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA856 + difference 0 1) (sourceB856 + difference 1 0) sourceC856) = raw14264 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14264; decide +kernel
    rw [ha]
    exact (canonical14264 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA856 + difference 0 2) (sourceB856 + difference 2 0) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA856 + difference 0 2) (sourceB856 + difference 2 0) sourceC856) = raw14265 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14265; decide +kernel
    rw [ha]
    exact (canonical14265 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA856 + difference 0 3) (sourceB856 + difference 3 0) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA856 + difference 0 3) (sourceB856 + difference 3 0) sourceC856) = raw5431 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5431; decide +kernel
    rw [ha]
    exact (canonical5431 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA856 + difference 0 4) (sourceB856 + difference 4 0) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA856 + difference 0 4) (sourceB856 + difference 4 0) sourceC856) = raw14266 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14266; decide +kernel
    rw [ha]
    exact (canonical14266 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA856 + difference 0 5) (sourceB856 + difference 5 0) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA856 + difference 0 5) (sourceB856 + difference 5 0) sourceC856) = raw14267 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14267; decide +kernel
    rw [ha]
    exact (canonical14267 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA856 + difference 1 0) (sourceB856 + difference 0 1) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA856 + difference 1 0) (sourceB856 + difference 0 1) sourceC856) = raw14268 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14268; decide +kernel
    rw [ha]
    exact (canonical14268 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA856 + difference 1 2) (sourceB856 + difference 2 1) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA856 + difference 1 2) (sourceB856 + difference 2 1) sourceC856) = raw14269 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14269; decide +kernel
    rw [ha]
    exact (canonical14269 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA856 + difference 1 3) (sourceB856 + difference 3 1) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA856 + difference 1 3) (sourceB856 + difference 3 1) sourceC856) = raw5436 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5436; decide +kernel
    rw [ha]
    exact (canonical5436 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA856 + difference 1 4) (sourceB856 + difference 4 1) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA856 + difference 1 4) (sourceB856 + difference 4 1) sourceC856) = raw14270 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14270; decide +kernel
    rw [ha]
    exact (canonical14270 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA856 + difference 1 5) (sourceB856 + difference 5 1) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA856 + difference 1 5) (sourceB856 + difference 5 1) sourceC856) = raw14271 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14271; decide +kernel
    rw [ha]
    exact (canonical14271 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA856 + difference 2 0) (sourceB856 + difference 0 2) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA856 + difference 2 0) (sourceB856 + difference 0 2) sourceC856) = raw14272 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14272; decide +kernel
    rw [ha]
    exact (canonical14272 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA856 + difference 2 1) (sourceB856 + difference 1 2) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA856 + difference 2 1) (sourceB856 + difference 1 2) sourceC856) = raw14273 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14273; decide +kernel
    rw [ha]
    exact (canonical14273 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA856 + difference 2 3) (sourceB856 + difference 3 2) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA856 + difference 2 3) (sourceB856 + difference 3 2) sourceC856) = raw5441 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5441; decide +kernel
    rw [ha]
    exact (canonical5441 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA856 + difference 2 4) (sourceB856 + difference 4 2) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA856 + difference 2 4) (sourceB856 + difference 4 2) sourceC856) = raw14274 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14274; decide +kernel
    rw [ha]
    exact (canonical14274 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA856 + difference 2 5) (sourceB856 + difference 5 2) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA856 + difference 2 5) (sourceB856 + difference 5 2) sourceC856) = raw14275 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14275; decide +kernel
    rw [ha]
    exact (canonical14275 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA856 + difference 3 0) (sourceB856 + difference 0 3) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4438) := by
    have ha : (tripleCharges (sourceA856 + difference 3 0) (sourceB856 + difference 0 3) sourceC856) = raw14276 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14276; decide +kernel
    rw [ha]
    exact (canonical14276 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA856 + difference 3 1) (sourceB856 + difference 1 3) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA856 + difference 3 1) (sourceB856 + difference 1 3) sourceC856) = raw14277 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14277; decide +kernel
    rw [ha]
    exact (canonical14277 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA856 + difference 3 2) (sourceB856 + difference 2 3) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA856 + difference 3 2) (sourceB856 + difference 2 3) sourceC856) = raw14278 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14278; decide +kernel
    rw [ha]
    exact (canonical14278 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA856 + difference 3 4) (sourceB856 + difference 4 3) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA856 + difference 3 4) (sourceB856 + difference 4 3) sourceC856) = raw14279 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14279; decide +kernel
    rw [ha]
    exact (canonical14279 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA856 + difference 3 5) (sourceB856 + difference 5 3) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA856 + difference 3 5) (sourceB856 + difference 5 3) sourceC856) = raw14280 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14280; decide +kernel
    rw [ha]
    exact (canonical14280 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA856 + difference 4 0) (sourceB856 + difference 0 4) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA856 + difference 4 0) (sourceB856 + difference 0 4) sourceC856) = raw14281 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14281; decide +kernel
    rw [ha]
    exact (canonical14281 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA856 + difference 4 1) (sourceB856 + difference 1 4) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA856 + difference 4 1) (sourceB856 + difference 1 4) sourceC856) = raw14282 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14282; decide +kernel
    rw [ha]
    exact (canonical14282 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA856 + difference 4 2) (sourceB856 + difference 2 4) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA856 + difference 4 2) (sourceB856 + difference 2 4) sourceC856) = raw14283 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14283; decide +kernel
    rw [ha]
    exact (canonical14283 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA856 + difference 4 3) (sourceB856 + difference 3 4) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA856 + difference 4 3) (sourceB856 + difference 3 4) sourceC856) = raw5451 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5451; decide +kernel
    rw [ha]
    exact (canonical5451 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA856 + difference 4 5) (sourceB856 + difference 5 4) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA856 + difference 4 5) (sourceB856 + difference 5 4) sourceC856) = raw14284 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14284; decide +kernel
    rw [ha]
    exact (canonical14284 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA856 + difference 5 0) (sourceB856 + difference 0 5) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA856 + difference 5 0) (sourceB856 + difference 0 5) sourceC856) = raw5442 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5442; decide +kernel
    rw [ha]
    exact (canonical5442 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA856 + difference 5 1) (sourceB856 + difference 1 5) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA856 + difference 5 1) (sourceB856 + difference 1 5) sourceC856) = raw5443 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5443; decide +kernel
    rw [ha]
    exact (canonical5443 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA856 + difference 5 2) (sourceB856 + difference 2 5) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA856 + difference 5 2) (sourceB856 + difference 2 5) sourceC856) = raw5444 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5444; decide +kernel
    rw [ha]
    exact (canonical5444 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA856 + difference 5 3) (sourceB856 + difference 3 5) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA856 + difference 5 3) (sourceB856 + difference 3 5) sourceC856) = raw14285 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14285; decide +kernel
    rw [ha]
    exact (canonical14285 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA856 + difference 5 4) (sourceB856 + difference 4 5) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA856 + difference 5 4) (sourceB856 + difference 4 5) sourceC856) = raw5445 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5445; decide +kernel
    rw [ha]
    exact (canonical5445 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA856 sourceB856 sourceC856
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm856, Integer.Sparse.eval]
  linarith only [hs]

def sourceA857 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB857 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC857 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm857 : Integer.Sparse Master := [(Sum.inr 1705, 1), (Sum.inr 1706, 2), (Sum.inr 1713, 2), (Sum.inr 2240, 2), (Sum.inr 2241, 2), (Sum.inr 2243, 2), (Sum.inr 2250, 4), (Sum.inr 2252, 2), (Sum.inr 2262, 2), (Sum.inr 2263, 4), (Sum.inr 2277, 2), (Sum.inr 2750, 2), (Sum.inr 2752, 1), (Sum.inr 2766, 2)]

theorem sourceEq857 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm857 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA857 + difference 0 1) (sourceB857 + difference 1 0) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA857 + difference 0 1) (sourceB857 + difference 1 0) sourceC857) = raw14286 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14286; decide +kernel
    rw [ha]
    exact (canonical14286 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA857 + difference 0 2) (sourceB857 + difference 2 0) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA857 + difference 0 2) (sourceB857 + difference 2 0) sourceC857) = raw14287 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14287; decide +kernel
    rw [ha]
    exact (canonical14287 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA857 + difference 0 3) (sourceB857 + difference 3 0) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2752) := by
    have ha : (tripleCharges (sourceA857 + difference 0 3) (sourceB857 + difference 3 0) sourceC857) = raw5491 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5491; decide +kernel
    rw [ha]
    exact (canonical5491 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA857 + difference 0 4) (sourceB857 + difference 4 0) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA857 + difference 0 4) (sourceB857 + difference 4 0) sourceC857) = raw14288 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14288; decide +kernel
    rw [ha]
    exact (canonical14288 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA857 + difference 0 5) (sourceB857 + difference 5 0) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA857 + difference 0 5) (sourceB857 + difference 5 0) sourceC857) = raw14289 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14289; decide +kernel
    rw [ha]
    exact (canonical14289 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA857 + difference 1 0) (sourceB857 + difference 0 1) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA857 + difference 1 0) (sourceB857 + difference 0 1) sourceC857) = raw14290 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14290; decide +kernel
    rw [ha]
    exact (canonical14290 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA857 + difference 1 2) (sourceB857 + difference 2 1) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA857 + difference 1 2) (sourceB857 + difference 2 1) sourceC857) = raw14291 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14291; decide +kernel
    rw [ha]
    exact (canonical14291 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA857 + difference 1 3) (sourceB857 + difference 3 1) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA857 + difference 1 3) (sourceB857 + difference 3 1) sourceC857) = raw5496 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5496; decide +kernel
    rw [ha]
    exact (canonical5496 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA857 + difference 1 4) (sourceB857 + difference 4 1) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA857 + difference 1 4) (sourceB857 + difference 4 1) sourceC857) = raw14292 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14292; decide +kernel
    rw [ha]
    exact (canonical14292 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA857 + difference 1 5) (sourceB857 + difference 5 1) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA857 + difference 1 5) (sourceB857 + difference 5 1) sourceC857) = raw14293 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14293; decide +kernel
    rw [ha]
    exact (canonical14293 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA857 + difference 2 0) (sourceB857 + difference 0 2) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA857 + difference 2 0) (sourceB857 + difference 0 2) sourceC857) = raw14294 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14294; decide +kernel
    rw [ha]
    exact (canonical14294 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA857 + difference 2 1) (sourceB857 + difference 1 2) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA857 + difference 2 1) (sourceB857 + difference 1 2) sourceC857) = raw14295 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14295; decide +kernel
    rw [ha]
    exact (canonical14295 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA857 + difference 2 3) (sourceB857 + difference 3 2) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA857 + difference 2 3) (sourceB857 + difference 3 2) sourceC857) = raw5501 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5501; decide +kernel
    rw [ha]
    exact (canonical5501 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA857 + difference 2 4) (sourceB857 + difference 4 2) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA857 + difference 2 4) (sourceB857 + difference 4 2) sourceC857) = raw14296 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14296; decide +kernel
    rw [ha]
    exact (canonical14296 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA857 + difference 2 5) (sourceB857 + difference 5 2) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA857 + difference 2 5) (sourceB857 + difference 5 2) sourceC857) = raw14297 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14297; decide +kernel
    rw [ha]
    exact (canonical14297 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA857 + difference 3 0) (sourceB857 + difference 0 3) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA857 + difference 3 0) (sourceB857 + difference 0 3) sourceC857) = raw14298 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14298; decide +kernel
    rw [ha]
    exact (canonical14298 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA857 + difference 3 1) (sourceB857 + difference 1 3) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA857 + difference 3 1) (sourceB857 + difference 1 3) sourceC857) = raw14299 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14299; decide +kernel
    rw [ha]
    exact (canonical14299 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA857 + difference 3 2) (sourceB857 + difference 2 3) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA857 + difference 3 2) (sourceB857 + difference 2 3) sourceC857) = raw14300 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14300; decide +kernel
    rw [ha]
    exact (canonical14300 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA857 + difference 3 4) (sourceB857 + difference 4 3) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA857 + difference 3 4) (sourceB857 + difference 4 3) sourceC857) = raw14301 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14301; decide +kernel
    rw [ha]
    exact (canonical14301 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA857 + difference 3 5) (sourceB857 + difference 5 3) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA857 + difference 3 5) (sourceB857 + difference 5 3) sourceC857) = raw14302 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14302; decide +kernel
    rw [ha]
    exact (canonical14302 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA857 + difference 4 0) (sourceB857 + difference 0 4) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA857 + difference 4 0) (sourceB857 + difference 0 4) sourceC857) = raw14303 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14303; decide +kernel
    rw [ha]
    exact (canonical14303 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA857 + difference 4 1) (sourceB857 + difference 1 4) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA857 + difference 4 1) (sourceB857 + difference 1 4) sourceC857) = raw14304 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14304; decide +kernel
    rw [ha]
    exact (canonical14304 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA857 + difference 4 2) (sourceB857 + difference 2 4) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA857 + difference 4 2) (sourceB857 + difference 2 4) sourceC857) = raw14305 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14305; decide +kernel
    rw [ha]
    exact (canonical14305 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA857 + difference 4 3) (sourceB857 + difference 3 4) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA857 + difference 4 3) (sourceB857 + difference 3 4) sourceC857) = raw5511 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5511; decide +kernel
    rw [ha]
    exact (canonical5511 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA857 + difference 4 5) (sourceB857 + difference 5 4) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA857 + difference 4 5) (sourceB857 + difference 5 4) sourceC857) = raw14306 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14306; decide +kernel
    rw [ha]
    exact (canonical14306 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA857 + difference 5 0) (sourceB857 + difference 0 5) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA857 + difference 5 0) (sourceB857 + difference 0 5) sourceC857) = raw5502 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5502; decide +kernel
    rw [ha]
    exact (canonical5502 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA857 + difference 5 1) (sourceB857 + difference 1 5) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA857 + difference 5 1) (sourceB857 + difference 1 5) sourceC857) = raw5503 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5503; decide +kernel
    rw [ha]
    exact (canonical5503 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA857 + difference 5 2) (sourceB857 + difference 2 5) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA857 + difference 5 2) (sourceB857 + difference 2 5) sourceC857) = raw5504 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5504; decide +kernel
    rw [ha]
    exact (canonical5504 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA857 + difference 5 3) (sourceB857 + difference 3 5) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA857 + difference 5 3) (sourceB857 + difference 3 5) sourceC857) = raw14307 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14307; decide +kernel
    rw [ha]
    exact (canonical14307 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA857 + difference 5 4) (sourceB857 + difference 4 5) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA857 + difference 5 4) (sourceB857 + difference 4 5) sourceC857) = raw5505 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5505; decide +kernel
    rw [ha]
    exact (canonical5505 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA857 sourceB857 sourceC857
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm857, Integer.Sparse.eval]
  linarith only [hs]

def sourceA858 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB858 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC858 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceForm858 : Integer.Sparse Master := [(Sum.inr 4248, 1), (Sum.inr 4249, 4), (Sum.inr 4801, 4), (Sum.inr 4802, 8), (Sum.inr 4831, 4), (Sum.inr 4888, 4), (Sum.inr 5433, 4), (Sum.inr 5452, 1)]

theorem sourceEq858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm858 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA858 + difference 0 1) (sourceB858 + difference 1 0) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA858 + difference 0 1) (sourceB858 + difference 1 0) sourceC858) = raw14308 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14308; decide +kernel
    rw [ha]
    exact (canonical14308 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA858 + difference 0 2) (sourceB858 + difference 2 0) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA858 + difference 0 2) (sourceB858 + difference 2 0) sourceC858) = raw14309 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14309; decide +kernel
    rw [ha]
    exact (canonical14309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA858 + difference 0 3) (sourceB858 + difference 3 0) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA858 + difference 0 3) (sourceB858 + difference 3 0) sourceC858) = raw11319 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11319; decide +kernel
    rw [ha]
    exact (canonical11319 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA858 + difference 0 4) (sourceB858 + difference 4 0) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA858 + difference 0 4) (sourceB858 + difference 4 0) sourceC858) = raw14310 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14310; decide +kernel
    rw [ha]
    exact (canonical14310 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA858 + difference 0 5) (sourceB858 + difference 5 0) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA858 + difference 0 5) (sourceB858 + difference 5 0) sourceC858) = raw14311 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14311; decide +kernel
    rw [ha]
    exact (canonical14311 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA858 + difference 1 0) (sourceB858 + difference 0 1) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA858 + difference 1 0) (sourceB858 + difference 0 1) sourceC858) = raw14312 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14312; decide +kernel
    rw [ha]
    exact (canonical14312 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA858 + difference 1 2) (sourceB858 + difference 2 1) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA858 + difference 1 2) (sourceB858 + difference 2 1) sourceC858) = raw14313 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14313; decide +kernel
    rw [ha]
    exact (canonical14313 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA858 + difference 1 3) (sourceB858 + difference 3 1) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA858 + difference 1 3) (sourceB858 + difference 3 1) sourceC858) = raw11324 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11324; decide +kernel
    rw [ha]
    exact (canonical11324 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA858 + difference 1 4) (sourceB858 + difference 4 1) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 1 4) (sourceB858 + difference 4 1) sourceC858) = raw14314 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14314; decide +kernel
    rw [ha]
    exact (canonical14314 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA858 + difference 1 5) (sourceB858 + difference 5 1) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 1 5) (sourceB858 + difference 5 1) sourceC858) = raw14315 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14315; decide +kernel
    rw [ha]
    exact (canonical14315 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA858 + difference 2 0) (sourceB858 + difference 0 2) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA858 + difference 2 0) (sourceB858 + difference 0 2) sourceC858) = raw14316 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14316; decide +kernel
    rw [ha]
    exact (canonical14316 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA858 + difference 2 1) (sourceB858 + difference 1 2) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA858 + difference 2 1) (sourceB858 + difference 1 2) sourceC858) = raw14317 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14317; decide +kernel
    rw [ha]
    exact (canonical14317 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA858 + difference 2 3) (sourceB858 + difference 3 2) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA858 + difference 2 3) (sourceB858 + difference 3 2) sourceC858) = raw11329 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11329; decide +kernel
    rw [ha]
    exact (canonical11329 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA858 + difference 2 4) (sourceB858 + difference 4 2) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 2 4) (sourceB858 + difference 4 2) sourceC858) = raw14318 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14318; decide +kernel
    rw [ha]
    exact (canonical14318 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA858 + difference 2 5) (sourceB858 + difference 5 2) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 2 5) (sourceB858 + difference 5 2) sourceC858) = raw14319 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14319; decide +kernel
    rw [ha]
    exact (canonical14319 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA858 + difference 3 0) (sourceB858 + difference 0 3) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4248) := by
    have ha : (tripleCharges (sourceA858 + difference 3 0) (sourceB858 + difference 0 3) sourceC858) = raw14320 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14320; decide +kernel
    rw [ha]
    exact (canonical14320 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA858 + difference 3 1) (sourceB858 + difference 1 3) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA858 + difference 3 1) (sourceB858 + difference 1 3) sourceC858) = raw14321 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14321; decide +kernel
    rw [ha]
    exact (canonical14321 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA858 + difference 3 2) (sourceB858 + difference 2 3) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA858 + difference 3 2) (sourceB858 + difference 2 3) sourceC858) = raw14322 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14322; decide +kernel
    rw [ha]
    exact (canonical14322 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA858 + difference 3 4) (sourceB858 + difference 4 3) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA858 + difference 3 4) (sourceB858 + difference 4 3) sourceC858) = raw14323 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14323; decide +kernel
    rw [ha]
    exact (canonical14323 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA858 + difference 3 5) (sourceB858 + difference 5 3) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA858 + difference 3 5) (sourceB858 + difference 5 3) sourceC858) = raw14324 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14324; decide +kernel
    rw [ha]
    exact (canonical14324 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA858 + difference 4 0) (sourceB858 + difference 0 4) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA858 + difference 4 0) (sourceB858 + difference 0 4) sourceC858) = raw14325 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14325; decide +kernel
    rw [ha]
    exact (canonical14325 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA858 + difference 4 1) (sourceB858 + difference 1 4) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 4 1) (sourceB858 + difference 1 4) sourceC858) = raw14326 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14326; decide +kernel
    rw [ha]
    exact (canonical14326 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA858 + difference 4 2) (sourceB858 + difference 2 4) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 4 2) (sourceB858 + difference 2 4) sourceC858) = raw14327 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14327; decide +kernel
    rw [ha]
    exact (canonical14327 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA858 + difference 4 3) (sourceB858 + difference 3 4) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA858 + difference 4 3) (sourceB858 + difference 3 4) sourceC858) = raw11339 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11339; decide +kernel
    rw [ha]
    exact (canonical11339 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA858 + difference 4 5) (sourceB858 + difference 5 4) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA858 + difference 4 5) (sourceB858 + difference 5 4) sourceC858) = raw14328 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14328; decide +kernel
    rw [ha]
    exact (canonical14328 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA858 + difference 5 0) (sourceB858 + difference 0 5) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA858 + difference 5 0) (sourceB858 + difference 0 5) sourceC858) = raw11330 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11330; decide +kernel
    rw [ha]
    exact (canonical11330 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA858 + difference 5 1) (sourceB858 + difference 1 5) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 5 1) (sourceB858 + difference 1 5) sourceC858) = raw11331 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11331; decide +kernel
    rw [ha]
    exact (canonical11331 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA858 + difference 5 2) (sourceB858 + difference 2 5) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 5 2) (sourceB858 + difference 2 5) sourceC858) = raw11332 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11332; decide +kernel
    rw [ha]
    exact (canonical11332 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA858 + difference 5 3) (sourceB858 + difference 3 5) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA858 + difference 5 3) (sourceB858 + difference 3 5) sourceC858) = raw14329 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14329; decide +kernel
    rw [ha]
    exact (canonical14329 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA858 + difference 5 4) (sourceB858 + difference 4 5) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA858 + difference 5 4) (sourceB858 + difference 4 5) sourceC858) = raw11333 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11333; decide +kernel
    rw [ha]
    exact (canonical11333 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA858 sourceB858 sourceC858
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm858, Integer.Sparse.eval]
  linarith only [hs]

def sourceA859 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB859 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC859 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceForm859 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4456, 1), (Sum.inr 4458, 2), (Sum.inr 4461, 1), (Sum.inr 4497, 1), (Sum.inr 4802, 2), (Sum.inr 4805, 1), (Sum.inr 4833, 1), (Sum.inr 4864, 1), (Sum.inr 4866, 2), (Sum.inr 4869, 1), (Sum.inr 4887, 2), (Sum.inr 4888, 2), (Sum.inr 4889, 2), (Sum.inr 4893, 3), (Sum.inr 4895, 2), (Sum.inr 5257, 1), (Sum.inr 5290, 1), (Sum.inr 5292, 2), (Sum.inr 5307, 1)]

theorem sourceEq859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm859 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA859 + difference 0 1) (sourceB859 + difference 1 0) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA859 + difference 0 1) (sourceB859 + difference 1 0) sourceC859) = raw14330 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14330; decide +kernel
    rw [ha]
    exact (canonical14330 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA859 + difference 0 2) (sourceB859 + difference 2 0) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA859 + difference 0 2) (sourceB859 + difference 2 0) sourceC859) = raw14331 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14331; decide +kernel
    rw [ha]
    exact (canonical14331 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA859 + difference 0 3) (sourceB859 + difference 3 0) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA859 + difference 0 3) (sourceB859 + difference 3 0) sourceC859) = raw14332 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14332; decide +kernel
    rw [ha]
    exact (canonical14332 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA859 + difference 0 4) (sourceB859 + difference 4 0) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA859 + difference 0 4) (sourceB859 + difference 4 0) sourceC859) = raw14333 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14333; decide +kernel
    rw [ha]
    exact (canonical14333 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA859 + difference 0 5) (sourceB859 + difference 5 0) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA859 + difference 0 5) (sourceB859 + difference 5 0) sourceC859) = raw14334 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14334; decide +kernel
    rw [ha]
    exact (canonical14334 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA859 + difference 1 0) (sourceB859 + difference 0 1) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA859 + difference 1 0) (sourceB859 + difference 0 1) sourceC859) = raw14335 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14335; decide +kernel
    rw [ha]
    exact (canonical14335 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA859 + difference 1 2) (sourceB859 + difference 2 1) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA859 + difference 1 2) (sourceB859 + difference 2 1) sourceC859) = raw14336 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14336; decide +kernel
    rw [ha]
    exact (canonical14336 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA859 + difference 1 3) (sourceB859 + difference 3 1) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA859 + difference 1 3) (sourceB859 + difference 3 1) sourceC859) = raw14337 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14337; decide +kernel
    rw [ha]
    exact (canonical14337 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA859 + difference 1 4) (sourceB859 + difference 4 1) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA859 + difference 1 4) (sourceB859 + difference 4 1) sourceC859) = raw14338 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14338; decide +kernel
    rw [ha]
    exact (canonical14338 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA859 + difference 1 5) (sourceB859 + difference 5 1) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA859 + difference 1 5) (sourceB859 + difference 5 1) sourceC859) = raw14339 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14339; decide +kernel
    rw [ha]
    exact (canonical14339 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA859 + difference 2 0) (sourceB859 + difference 0 2) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA859 + difference 2 0) (sourceB859 + difference 0 2) sourceC859) = raw14340 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14340; decide +kernel
    rw [ha]
    exact (canonical14340 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA859 + difference 2 1) (sourceB859 + difference 1 2) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA859 + difference 2 1) (sourceB859 + difference 1 2) sourceC859) = raw14341 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14341; decide +kernel
    rw [ha]
    exact (canonical14341 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA859 + difference 2 3) (sourceB859 + difference 3 2) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA859 + difference 2 3) (sourceB859 + difference 3 2) sourceC859) = raw14342 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14342; decide +kernel
    rw [ha]
    exact (canonical14342 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA859 + difference 2 4) (sourceB859 + difference 4 2) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA859 + difference 2 4) (sourceB859 + difference 4 2) sourceC859) = raw14343 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14343; decide +kernel
    rw [ha]
    exact (canonical14343 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA859 + difference 2 5) (sourceB859 + difference 5 2) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA859 + difference 2 5) (sourceB859 + difference 5 2) sourceC859) = raw14344 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14344; decide +kernel
    rw [ha]
    exact (canonical14344 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA859 + difference 3 0) (sourceB859 + difference 0 3) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA859 + difference 3 0) (sourceB859 + difference 0 3) sourceC859) = raw14345 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14345; decide +kernel
    rw [ha]
    exact (canonical14345 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA859 + difference 3 1) (sourceB859 + difference 1 3) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA859 + difference 3 1) (sourceB859 + difference 1 3) sourceC859) = raw14346 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14346; decide +kernel
    rw [ha]
    exact (canonical14346 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA859 + difference 3 2) (sourceB859 + difference 2 3) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA859 + difference 3 2) (sourceB859 + difference 2 3) sourceC859) = raw14347 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14347; decide +kernel
    rw [ha]
    exact (canonical14347 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA859 + difference 3 4) (sourceB859 + difference 4 3) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA859 + difference 3 4) (sourceB859 + difference 4 3) sourceC859) = raw14348 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14348; decide +kernel
    rw [ha]
    exact (canonical14348 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA859 + difference 3 5) (sourceB859 + difference 5 3) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA859 + difference 3 5) (sourceB859 + difference 5 3) sourceC859) = raw14349 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14349; decide +kernel
    rw [ha]
    exact (canonical14349 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA859 + difference 4 0) (sourceB859 + difference 0 4) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA859 + difference 4 0) (sourceB859 + difference 0 4) sourceC859) = raw14350 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14350; decide +kernel
    rw [ha]
    exact (canonical14350 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA859 + difference 4 1) (sourceB859 + difference 1 4) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA859 + difference 4 1) (sourceB859 + difference 1 4) sourceC859) = raw14351 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14351; decide +kernel
    rw [ha]
    exact (canonical14351 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA859 + difference 4 2) (sourceB859 + difference 2 4) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA859 + difference 4 2) (sourceB859 + difference 2 4) sourceC859) = raw14352 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14352; decide +kernel
    rw [ha]
    exact (canonical14352 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA859 + difference 4 3) (sourceB859 + difference 3 4) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA859 + difference 4 3) (sourceB859 + difference 3 4) sourceC859) = raw14353 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14353; decide +kernel
    rw [ha]
    exact (canonical14353 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA859 + difference 4 5) (sourceB859 + difference 5 4) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA859 + difference 4 5) (sourceB859 + difference 5 4) sourceC859) = raw14354 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14354; decide +kernel
    rw [ha]
    exact (canonical14354 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA859 + difference 5 0) (sourceB859 + difference 0 5) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA859 + difference 5 0) (sourceB859 + difference 0 5) sourceC859) = raw14355 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14355; decide +kernel
    rw [ha]
    exact (canonical14355 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA859 + difference 5 1) (sourceB859 + difference 1 5) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA859 + difference 5 1) (sourceB859 + difference 1 5) sourceC859) = raw14356 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14356; decide +kernel
    rw [ha]
    exact (canonical14356 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA859 + difference 5 2) (sourceB859 + difference 2 5) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA859 + difference 5 2) (sourceB859 + difference 2 5) sourceC859) = raw14357 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14357; decide +kernel
    rw [ha]
    exact (canonical14357 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA859 + difference 5 3) (sourceB859 + difference 3 5) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA859 + difference 5 3) (sourceB859 + difference 3 5) sourceC859) = raw14358 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14358; decide +kernel
    rw [ha]
    exact (canonical14358 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA859 + difference 5 4) (sourceB859 + difference 4 5) sourceC859) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA859 + difference 5 4) (sourceB859 + difference 4 5) sourceC859) = raw14359 := by
      apply Matrix.ext; unfold tripleCharges sourceA859 sourceB859 sourceC859 difference raw14359; decide +kernel
    rw [ha]
    exact (canonical14359 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA859 sourceB859 sourceC859
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm859, Integer.Sparse.eval]
  linarith only [hs]

def sourceA860 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB860 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC860 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm860 : Integer.Sparse Master := [(Sum.inr 4068, 2), (Sum.inr 4069, 3), (Sum.inr 4079, 2), (Sum.inr 4080, 6), (Sum.inr 4083, 6), (Sum.inr 4084, 6), (Sum.inr 4091, 2), (Sum.inr 4093, 3)]

theorem sourceEq860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm860 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA860 + difference 0 1) (sourceB860 + difference 1 0) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA860 + difference 0 1) (sourceB860 + difference 1 0) sourceC860) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA860 + difference 0 2) (sourceB860 + difference 2 0) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA860 + difference 0 2) (sourceB860 + difference 2 0) sourceC860) = raw3333 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw3333; decide +kernel
    rw [ha]
    exact (canonical3333 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA860 + difference 0 3) (sourceB860 + difference 3 0) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA860 + difference 0 3) (sourceB860 + difference 3 0) sourceC860) = raw2933 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw2933; decide +kernel
    rw [ha]
    exact (canonical2933 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA860 + difference 0 4) (sourceB860 + difference 4 0) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA860 + difference 0 4) (sourceB860 + difference 4 0) sourceC860) = raw2928 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw2928; decide +kernel
    rw [ha]
    exact (canonical2928 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA860 + difference 0 5) (sourceB860 + difference 5 0) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA860 + difference 0 5) (sourceB860 + difference 5 0) sourceC860) = raw3334 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw3334; decide +kernel
    rw [ha]
    exact (canonical3334 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA860 + difference 1 0) (sourceB860 + difference 0 1) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA860 + difference 1 0) (sourceB860 + difference 0 1) sourceC860) = raw14360 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14360; decide +kernel
    rw [ha]
    exact (canonical14360 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA860 + difference 1 2) (sourceB860 + difference 2 1) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA860 + difference 1 2) (sourceB860 + difference 2 1) sourceC860) = raw14361 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14361; decide +kernel
    rw [ha]
    exact (canonical14361 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA860 + difference 1 3) (sourceB860 + difference 3 1) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA860 + difference 1 3) (sourceB860 + difference 3 1) sourceC860) = raw3323 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw3323; decide +kernel
    rw [ha]
    exact (canonical3323 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA860 + difference 1 4) (sourceB860 + difference 4 1) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA860 + difference 1 4) (sourceB860 + difference 4 1) sourceC860) = raw14362 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14362; decide +kernel
    rw [ha]
    exact (canonical14362 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA860 + difference 1 5) (sourceB860 + difference 5 1) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA860 + difference 1 5) (sourceB860 + difference 5 1) sourceC860) = raw14363 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14363; decide +kernel
    rw [ha]
    exact (canonical14363 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA860 + difference 2 0) (sourceB860 + difference 0 2) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA860 + difference 2 0) (sourceB860 + difference 0 2) sourceC860) = raw14364 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14364; decide +kernel
    rw [ha]
    exact (canonical14364 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA860 + difference 2 1) (sourceB860 + difference 1 2) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA860 + difference 2 1) (sourceB860 + difference 1 2) sourceC860) = raw14365 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14365; decide +kernel
    rw [ha]
    exact (canonical14365 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA860 + difference 2 3) (sourceB860 + difference 3 2) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA860 + difference 2 3) (sourceB860 + difference 3 2) sourceC860) = raw3327 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw3327; decide +kernel
    rw [ha]
    exact (canonical3327 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA860 + difference 2 4) (sourceB860 + difference 4 2) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA860 + difference 2 4) (sourceB860 + difference 4 2) sourceC860) = raw14366 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14366; decide +kernel
    rw [ha]
    exact (canonical14366 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA860 + difference 2 5) (sourceB860 + difference 5 2) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA860 + difference 2 5) (sourceB860 + difference 5 2) sourceC860) = raw14367 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14367; decide +kernel
    rw [ha]
    exact (canonical14367 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA860 + difference 3 0) (sourceB860 + difference 0 3) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA860 + difference 3 0) (sourceB860 + difference 0 3) sourceC860) = raw14368 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14368; decide +kernel
    rw [ha]
    exact (canonical14368 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA860 + difference 3 1) (sourceB860 + difference 1 3) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA860 + difference 3 1) (sourceB860 + difference 1 3) sourceC860) = raw14369 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14369; decide +kernel
    rw [ha]
    exact (canonical14369 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA860 + difference 3 2) (sourceB860 + difference 2 3) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA860 + difference 3 2) (sourceB860 + difference 2 3) sourceC860) = raw14370 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14370; decide +kernel
    rw [ha]
    exact (canonical14370 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA860 + difference 3 4) (sourceB860 + difference 4 3) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA860 + difference 3 4) (sourceB860 + difference 4 3) sourceC860) = raw14371 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14371; decide +kernel
    rw [ha]
    exact (canonical14371 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA860 + difference 3 5) (sourceB860 + difference 5 3) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA860 + difference 3 5) (sourceB860 + difference 5 3) sourceC860) = raw14372 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14372; decide +kernel
    rw [ha]
    exact (canonical14372 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA860 + difference 4 0) (sourceB860 + difference 0 4) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA860 + difference 4 0) (sourceB860 + difference 0 4) sourceC860) = raw14373 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14373; decide +kernel
    rw [ha]
    exact (canonical14373 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA860 + difference 4 1) (sourceB860 + difference 1 4) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA860 + difference 4 1) (sourceB860 + difference 1 4) sourceC860) = raw14374 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14374; decide +kernel
    rw [ha]
    exact (canonical14374 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA860 + difference 4 2) (sourceB860 + difference 2 4) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA860 + difference 4 2) (sourceB860 + difference 2 4) sourceC860) = raw14375 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14375; decide +kernel
    rw [ha]
    exact (canonical14375 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA860 + difference 4 3) (sourceB860 + difference 3 4) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA860 + difference 4 3) (sourceB860 + difference 3 4) sourceC860) = raw3335 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw3335; decide +kernel
    rw [ha]
    exact (canonical3335 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA860 + difference 4 5) (sourceB860 + difference 5 4) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA860 + difference 4 5) (sourceB860 + difference 5 4) sourceC860) = raw14376 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw14376; decide +kernel
    rw [ha]
    exact (canonical14376 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA860 + difference 5 0) (sourceB860 + difference 0 5) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA860 + difference 5 0) (sourceB860 + difference 0 5) sourceC860) = raw11537 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw11537; decide +kernel
    rw [ha]
    exact (canonical11537 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA860 + difference 5 1) (sourceB860 + difference 1 5) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA860 + difference 5 1) (sourceB860 + difference 1 5) sourceC860) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA860 + difference 5 2) (sourceB860 + difference 2 5) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA860 + difference 5 2) (sourceB860 + difference 2 5) sourceC860) = raw11539 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw11539; decide +kernel
    rw [ha]
    exact (canonical11539 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA860 + difference 5 3) (sourceB860 + difference 3 5) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA860 + difference 5 3) (sourceB860 + difference 3 5) sourceC860) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA860 + difference 5 4) (sourceB860 + difference 4 5) sourceC860) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA860 + difference 5 4) (sourceB860 + difference 4 5) sourceC860) = raw2924 := by
      apply Matrix.ext; unfold tripleCharges sourceA860 sourceB860 sourceC860 difference raw2924; decide +kernel
    rw [ha]
    exact (canonical2924 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA860 sourceB860 sourceC860
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm860, Integer.Sparse.eval]
  linarith only [hs]

def sourceA861 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB861 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC861 : Charge := ![2, 1, -1, -2, 0, 0]
def sourceForm861 : Integer.Sparse Master := [(Sum.inr 4733, 2), (Sum.inr 4735, 2), (Sum.inr 4891, 1), (Sum.inr 5068, 2), (Sum.inr 5074, 2), (Sum.inr 5086, 2), (Sum.inr 5254, 2), (Sum.inr 5322, 2), (Sum.inr 5353, 2), (Sum.inr 5360, 2), (Sum.inr 5402, 2), (Sum.inr 5405, 2), (Sum.inr 5406, 2), (Sum.inr 5407, 1), (Sum.inr 5411, 2), (Sum.inr 5412, 2)]

theorem sourceEq861 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm861 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA861 + difference 0 1) (sourceB861 + difference 1 0) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA861 + difference 0 1) (sourceB861 + difference 1 0) sourceC861) = raw14377 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14377; decide +kernel
    rw [ha]
    exact (canonical14377 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA861 + difference 0 2) (sourceB861 + difference 2 0) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA861 + difference 0 2) (sourceB861 + difference 2 0) sourceC861) = raw14378 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14378; decide +kernel
    rw [ha]
    exact (canonical14378 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA861 + difference 0 3) (sourceB861 + difference 3 0) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA861 + difference 0 3) (sourceB861 + difference 3 0) sourceC861) = raw14379 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14379; decide +kernel
    rw [ha]
    exact (canonical14379 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA861 + difference 0 4) (sourceB861 + difference 4 0) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA861 + difference 0 4) (sourceB861 + difference 4 0) sourceC861) = raw14380 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14380; decide +kernel
    rw [ha]
    exact (canonical14380 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA861 + difference 0 5) (sourceB861 + difference 5 0) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA861 + difference 0 5) (sourceB861 + difference 5 0) sourceC861) = raw14381 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14381; decide +kernel
    rw [ha]
    exact (canonical14381 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA861 + difference 1 0) (sourceB861 + difference 0 1) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA861 + difference 1 0) (sourceB861 + difference 0 1) sourceC861) = raw14382 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14382; decide +kernel
    rw [ha]
    exact (canonical14382 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA861 + difference 1 2) (sourceB861 + difference 2 1) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA861 + difference 1 2) (sourceB861 + difference 2 1) sourceC861) = raw14383 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14383; decide +kernel
    rw [ha]
    exact (canonical14383 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA861 + difference 1 3) (sourceB861 + difference 3 1) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA861 + difference 1 3) (sourceB861 + difference 3 1) sourceC861) = raw14384 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14384; decide +kernel
    rw [ha]
    exact (canonical14384 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA861 + difference 1 4) (sourceB861 + difference 4 1) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA861 + difference 1 4) (sourceB861 + difference 4 1) sourceC861) = raw14385 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14385; decide +kernel
    rw [ha]
    exact (canonical14385 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA861 + difference 1 5) (sourceB861 + difference 5 1) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA861 + difference 1 5) (sourceB861 + difference 5 1) sourceC861) = raw14386 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14386; decide +kernel
    rw [ha]
    exact (canonical14386 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA861 + difference 2 0) (sourceB861 + difference 0 2) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA861 + difference 2 0) (sourceB861 + difference 0 2) sourceC861) = raw14387 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14387; decide +kernel
    rw [ha]
    exact (canonical14387 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA861 + difference 2 1) (sourceB861 + difference 1 2) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA861 + difference 2 1) (sourceB861 + difference 1 2) sourceC861) = raw14388 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14388; decide +kernel
    rw [ha]
    exact (canonical14388 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA861 + difference 2 3) (sourceB861 + difference 3 2) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA861 + difference 2 3) (sourceB861 + difference 3 2) sourceC861) = raw14389 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14389; decide +kernel
    rw [ha]
    exact (canonical14389 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA861 + difference 2 4) (sourceB861 + difference 4 2) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA861 + difference 2 4) (sourceB861 + difference 4 2) sourceC861) = raw14390 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14390; decide +kernel
    rw [ha]
    exact (canonical14390 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA861 + difference 2 5) (sourceB861 + difference 5 2) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA861 + difference 2 5) (sourceB861 + difference 5 2) sourceC861) = raw14391 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14391; decide +kernel
    rw [ha]
    exact (canonical14391 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA861 + difference 3 0) (sourceB861 + difference 0 3) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA861 + difference 3 0) (sourceB861 + difference 0 3) sourceC861) = raw14392 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14392; decide +kernel
    rw [ha]
    exact (canonical14392 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA861 + difference 3 1) (sourceB861 + difference 1 3) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA861 + difference 3 1) (sourceB861 + difference 1 3) sourceC861) = raw14393 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14393; decide +kernel
    rw [ha]
    exact (canonical14393 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA861 + difference 3 2) (sourceB861 + difference 2 3) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA861 + difference 3 2) (sourceB861 + difference 2 3) sourceC861) = raw14394 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14394; decide +kernel
    rw [ha]
    exact (canonical14394 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA861 + difference 3 4) (sourceB861 + difference 4 3) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA861 + difference 3 4) (sourceB861 + difference 4 3) sourceC861) = raw14395 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14395; decide +kernel
    rw [ha]
    exact (canonical14395 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA861 + difference 3 5) (sourceB861 + difference 5 3) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA861 + difference 3 5) (sourceB861 + difference 5 3) sourceC861) = raw14396 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14396; decide +kernel
    rw [ha]
    exact (canonical14396 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA861 + difference 4 0) (sourceB861 + difference 0 4) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5068) := by
    have ha : (tripleCharges (sourceA861 + difference 4 0) (sourceB861 + difference 0 4) sourceC861) = raw14397 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14397; decide +kernel
    rw [ha]
    exact (canonical14397 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA861 + difference 4 1) (sourceB861 + difference 1 4) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5322) := by
    have ha : (tripleCharges (sourceA861 + difference 4 1) (sourceB861 + difference 1 4) sourceC861) = raw14398 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14398; decide +kernel
    rw [ha]
    exact (canonical14398 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA861 + difference 4 2) (sourceB861 + difference 2 4) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5322) := by
    have ha : (tripleCharges (sourceA861 + difference 4 2) (sourceB861 + difference 2 4) sourceC861) = raw14399 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14399; decide +kernel
    rw [ha]
    exact (canonical14399 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA861 + difference 4 3) (sourceB861 + difference 3 4) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5068) := by
    have ha : (tripleCharges (sourceA861 + difference 4 3) (sourceB861 + difference 3 4) sourceC861) = raw14400 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14400; decide +kernel
    rw [ha]
    exact (canonical14400 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA861 + difference 4 5) (sourceB861 + difference 5 4) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA861 + difference 4 5) (sourceB861 + difference 5 4) sourceC861) = raw14401 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14401; decide +kernel
    rw [ha]
    exact (canonical14401 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA861 + difference 5 0) (sourceB861 + difference 0 5) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4733) := by
    have ha : (tripleCharges (sourceA861 + difference 5 0) (sourceB861 + difference 0 5) sourceC861) = raw14402 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14402; decide +kernel
    rw [ha]
    exact (canonical14402 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA861 + difference 5 1) (sourceB861 + difference 1 5) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4735) := by
    have ha : (tripleCharges (sourceA861 + difference 5 1) (sourceB861 + difference 1 5) sourceC861) = raw14403 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14403; decide +kernel
    rw [ha]
    exact (canonical14403 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA861 + difference 5 2) (sourceB861 + difference 2 5) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4735) := by
    have ha : (tripleCharges (sourceA861 + difference 5 2) (sourceB861 + difference 2 5) sourceC861) = raw14404 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14404; decide +kernel
    rw [ha]
    exact (canonical14404 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA861 + difference 5 3) (sourceB861 + difference 3 5) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4733) := by
    have ha : (tripleCharges (sourceA861 + difference 5 3) (sourceB861 + difference 3 5) sourceC861) = raw14405 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14405; decide +kernel
    rw [ha]
    exact (canonical14405 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA861 + difference 5 4) (sourceB861 + difference 4 5) sourceC861) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA861 + difference 5 4) (sourceB861 + difference 4 5) sourceC861) = raw14406 := by
      apply Matrix.ext; unfold tripleCharges sourceA861 sourceB861 sourceC861 difference raw14406; decide +kernel
    rw [ha]
    exact (canonical14406 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA861 sourceB861 sourceC861
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm861, Integer.Sparse.eval]
  linarith only [hs]

def sourceA862 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB862 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC862 : Charge := ![2, 1, -1, -2, 0, 0]
def sourceForm862 : Integer.Sparse Master := [(Sum.inr 1902, 1), (Sum.inr 1904, 1), (Sum.inr 1910, 1), (Sum.inr 1923, 1), (Sum.inr 2253, 1), (Sum.inr 2970, 1), (Sum.inr 2974, 1), (Sum.inr 2984, 1), (Sum.inr 3016, 1), (Sum.inr 3463, 1), (Sum.inr 3464, 1), (Sum.inr 3473, 1), (Sum.inr 3528, 1), (Sum.inr 3648, 1), (Sum.inr 3658, 1), (Sum.inr 3761, 1), (Sum.inr 3762, 1), (Sum.inr 3780, 1), (Sum.inr 3783, 1), (Sum.inr 3788, 1), (Sum.inr 3800, 1), (Sum.inr 3801, 1), (Sum.inr 3802, 1), (Sum.inr 3803, 1), (Sum.inr 3813, 1), (Sum.inr 3814, 1), (Sum.inr 3847, 1), (Sum.inr 3856, 1), (Sum.inr 3883, 1), (Sum.inr 3977, 1)]

theorem sourceEq862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm862 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA862 + difference 0 1) (sourceB862 + difference 1 0) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA862 + difference 0 1) (sourceB862 + difference 1 0) sourceC862) = raw14407 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14407; decide +kernel
    rw [ha]
    exact (canonical14407 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA862 + difference 0 2) (sourceB862 + difference 2 0) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA862 + difference 0 2) (sourceB862 + difference 2 0) sourceC862) = raw14408 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14408; decide +kernel
    rw [ha]
    exact (canonical14408 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA862 + difference 0 3) (sourceB862 + difference 3 0) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA862 + difference 0 3) (sourceB862 + difference 3 0) sourceC862) = raw14409 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14409; decide +kernel
    rw [ha]
    exact (canonical14409 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA862 + difference 0 4) (sourceB862 + difference 4 0) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA862 + difference 0 4) (sourceB862 + difference 4 0) sourceC862) = raw14410 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14410; decide +kernel
    rw [ha]
    exact (canonical14410 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA862 + difference 0 5) (sourceB862 + difference 5 0) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA862 + difference 0 5) (sourceB862 + difference 5 0) sourceC862) = raw14411 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14411; decide +kernel
    rw [ha]
    exact (canonical14411 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA862 + difference 1 0) (sourceB862 + difference 0 1) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA862 + difference 1 0) (sourceB862 + difference 0 1) sourceC862) = raw14412 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14412; decide +kernel
    rw [ha]
    exact (canonical14412 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA862 + difference 1 2) (sourceB862 + difference 2 1) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA862 + difference 1 2) (sourceB862 + difference 2 1) sourceC862) = raw14413 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14413; decide +kernel
    rw [ha]
    exact (canonical14413 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA862 + difference 1 3) (sourceB862 + difference 3 1) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA862 + difference 1 3) (sourceB862 + difference 3 1) sourceC862) = raw14414 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14414; decide +kernel
    rw [ha]
    exact (canonical14414 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA862 + difference 1 4) (sourceB862 + difference 4 1) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA862 + difference 1 4) (sourceB862 + difference 4 1) sourceC862) = raw14415 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14415; decide +kernel
    rw [ha]
    exact (canonical14415 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA862 + difference 1 5) (sourceB862 + difference 5 1) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA862 + difference 1 5) (sourceB862 + difference 5 1) sourceC862) = raw14416 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14416; decide +kernel
    rw [ha]
    exact (canonical14416 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA862 + difference 2 0) (sourceB862 + difference 0 2) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA862 + difference 2 0) (sourceB862 + difference 0 2) sourceC862) = raw14417 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14417; decide +kernel
    rw [ha]
    exact (canonical14417 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA862 + difference 2 1) (sourceB862 + difference 1 2) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA862 + difference 2 1) (sourceB862 + difference 1 2) sourceC862) = raw14418 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14418; decide +kernel
    rw [ha]
    exact (canonical14418 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA862 + difference 2 3) (sourceB862 + difference 3 2) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA862 + difference 2 3) (sourceB862 + difference 3 2) sourceC862) = raw14419 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14419; decide +kernel
    rw [ha]
    exact (canonical14419 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA862 + difference 2 4) (sourceB862 + difference 4 2) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA862 + difference 2 4) (sourceB862 + difference 4 2) sourceC862) = raw14420 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14420; decide +kernel
    rw [ha]
    exact (canonical14420 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA862 + difference 2 5) (sourceB862 + difference 5 2) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA862 + difference 2 5) (sourceB862 + difference 5 2) sourceC862) = raw14421 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14421; decide +kernel
    rw [ha]
    exact (canonical14421 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA862 + difference 3 0) (sourceB862 + difference 0 3) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA862 + difference 3 0) (sourceB862 + difference 0 3) sourceC862) = raw14422 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14422; decide +kernel
    rw [ha]
    exact (canonical14422 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA862 + difference 3 1) (sourceB862 + difference 1 3) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA862 + difference 3 1) (sourceB862 + difference 1 3) sourceC862) = raw14423 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14423; decide +kernel
    rw [ha]
    exact (canonical14423 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA862 + difference 3 2) (sourceB862 + difference 2 3) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA862 + difference 3 2) (sourceB862 + difference 2 3) sourceC862) = raw14424 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14424; decide +kernel
    rw [ha]
    exact (canonical14424 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA862 + difference 3 4) (sourceB862 + difference 4 3) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA862 + difference 3 4) (sourceB862 + difference 4 3) sourceC862) = raw14425 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14425; decide +kernel
    rw [ha]
    exact (canonical14425 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA862 + difference 3 5) (sourceB862 + difference 5 3) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA862 + difference 3 5) (sourceB862 + difference 5 3) sourceC862) = raw14426 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14426; decide +kernel
    rw [ha]
    exact (canonical14426 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA862 + difference 4 0) (sourceB862 + difference 0 4) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2970) := by
    have ha : (tripleCharges (sourceA862 + difference 4 0) (sourceB862 + difference 0 4) sourceC862) = raw14427 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14427; decide +kernel
    rw [ha]
    exact (canonical14427 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA862 + difference 4 1) (sourceB862 + difference 1 4) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3648) := by
    have ha : (tripleCharges (sourceA862 + difference 4 1) (sourceB862 + difference 1 4) sourceC862) = raw14428 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14428; decide +kernel
    rw [ha]
    exact (canonical14428 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA862 + difference 4 2) (sourceB862 + difference 2 4) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3658) := by
    have ha : (tripleCharges (sourceA862 + difference 4 2) (sourceB862 + difference 2 4) sourceC862) = raw14429 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14429; decide +kernel
    rw [ha]
    exact (canonical14429 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA862 + difference 4 3) (sourceB862 + difference 3 4) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3473) := by
    have ha : (tripleCharges (sourceA862 + difference 4 3) (sourceB862 + difference 3 4) sourceC862) = raw14430 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14430; decide +kernel
    rw [ha]
    exact (canonical14430 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA862 + difference 4 5) (sourceB862 + difference 5 4) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA862 + difference 4 5) (sourceB862 + difference 5 4) sourceC862) = raw14431 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14431; decide +kernel
    rw [ha]
    exact (canonical14431 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA862 + difference 5 0) (sourceB862 + difference 0 5) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1902) := by
    have ha : (tripleCharges (sourceA862 + difference 5 0) (sourceB862 + difference 0 5) sourceC862) = raw14432 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14432; decide +kernel
    rw [ha]
    exact (canonical14432 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA862 + difference 5 1) (sourceB862 + difference 1 5) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1904) := by
    have ha : (tripleCharges (sourceA862 + difference 5 1) (sourceB862 + difference 1 5) sourceC862) = raw14433 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14433; decide +kernel
    rw [ha]
    exact (canonical14433 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA862 + difference 5 2) (sourceB862 + difference 2 5) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1923) := by
    have ha : (tripleCharges (sourceA862 + difference 5 2) (sourceB862 + difference 2 5) sourceC862) = raw14434 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14434; decide +kernel
    rw [ha]
    exact (canonical14434 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA862 + difference 5 3) (sourceB862 + difference 3 5) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1910) := by
    have ha : (tripleCharges (sourceA862 + difference 5 3) (sourceB862 + difference 3 5) sourceC862) = raw14435 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14435; decide +kernel
    rw [ha]
    exact (canonical14435 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA862 + difference 5 4) (sourceB862 + difference 4 5) sourceC862) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA862 + difference 5 4) (sourceB862 + difference 4 5) sourceC862) = raw14436 := by
      apply Matrix.ext; unfold tripleCharges sourceA862 sourceB862 sourceC862 difference raw14436; decide +kernel
    rw [ha]
    exact (canonical14436 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA862 sourceB862 sourceC862
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm862, Integer.Sparse.eval]
  linarith only [hs]

def sourceA863 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB863 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC863 : Charge := ![2, 1, -1, -2, 0, 0]
def sourceForm863 : Integer.Sparse Master := [(Sum.inr 2481, 1), (Sum.inr 3691, 1), (Sum.inr 3788, 1), (Sum.inr 3803, 1), (Sum.inr 3805, 1), (Sum.inr 3809, 1), (Sum.inr 4092, -1)]

theorem sourceEq863 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm863 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA863 + difference 0 0) (sourceB863 + difference 0 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA863 + difference 0 0) (sourceB863 + difference 0 0) sourceC863) = raw14437 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14437; decide +kernel
    rw [ha]
    exact (canonical14437 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA863 + difference 0 1) (sourceB863 + difference 1 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA863 + difference 0 1) (sourceB863 + difference 1 0) sourceC863) = raw14438 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14438; decide +kernel
    rw [ha]
    exact (canonical14438 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA863 + difference 0 2) (sourceB863 + difference 2 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA863 + difference 0 2) (sourceB863 + difference 2 0) sourceC863) = raw14439 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14439; decide +kernel
    rw [ha]
    exact (canonical14439 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA863 + difference 0 3) (sourceB863 + difference 3 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA863 + difference 0 3) (sourceB863 + difference 3 0) sourceC863) = raw14440 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14440; decide +kernel
    rw [ha]
    exact (canonical14440 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA863 + difference 0 4) (sourceB863 + difference 4 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA863 + difference 0 4) (sourceB863 + difference 4 0) sourceC863) = raw14441 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14441; decide +kernel
    rw [ha]
    exact (canonical14441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA863 + difference 0 5) (sourceB863 + difference 5 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA863 + difference 0 5) (sourceB863 + difference 5 0) sourceC863) = raw14442 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14442; decide +kernel
    rw [ha]
    exact (canonical14442 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA863 + sourceB863) sourceC863) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA863 + sourceB863) sourceC863) = raw14443 := by
      apply Matrix.ext; unfold doubleCharges sourceA863 sourceB863 sourceC863 raw14443; decide +kernel
    rw [ha]
    exact (canonical14443 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA863 sourceB863 sourceC863
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm863, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
