import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoarseGroupRingCohomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CohomologicalFiniteness

namespace OAI

/-! # The cohomological part of Poincare duality transfer

Coarse invariance supplies the vanishing and the integral top class. Existence
of a finite projective resolution is a separate algebraic finiteness obligation.
-/

namespace PolycyclicRecognition
open CategoryTheory
variable {G H : Type} [Group G] [Group H]

theorem poincareDuality_of_coarse_finiteResolution (e : GroupCoarseEquivalence G H)
    (hfin : HasFiniteProjectiveResolution H) {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) : IsIntegralPoincareDualityGroup H n := by
  refine ⟨hfin, ?_, ?_⟩
  · intro i hi
    exact (hG.2.1 i hi).of_iso (coarseGroupRingCohomologyIso (R := ℤ) e i).symm
  · obtain ⟨top⟩ := hG.2.2
    exact ⟨(coarseGroupRingCohomologyIso (R := ℤ) e n).symm ≪≫ top⟩

end PolycyclicRecognition

end OAI
