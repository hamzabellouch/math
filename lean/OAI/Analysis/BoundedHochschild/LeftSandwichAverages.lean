import OAI.Analysis.BoundedHochschild.CompletelyBoundedArithmetic
import OAI.Analysis.BoundedHochschild.RightAveragingOrbit

namespace OAI

/-! Input and output left multiplication commute with right averaging,
including on the weak-star orbit closure. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma leftSandwichMap_rightAverage {I : Type*} [Fintype I]
    (a b : M) (m : I → M) (T : M →L[ℂ] M) :
    leftSandwichMap a b (finiteRightAverage m T) =
      finiteRightAverage m (leftSandwichMap a b T) := by
  ext x
  simp only [leftSandwichMap_apply, finiteRightAverage_apply, Finset.mul_sum, mul_assoc]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def weakLeftSandwich (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M)
    (F : M → WeakDual ℂ X) : M → WeakDual ℂ X :=
  fun x => weakDualOperator e (ContinuousLinearMap.mul ℂ M a) (F (b * x))

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakLeftSandwich_image (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (a b : M) (T : M →L[ℂ] M) :
    weakLeftSandwich e a b (weakOperatorImage e T) =
      weakOperatorImage e (leftSandwichMap a b T) := by
  funext x
  exact weakDualOperator_image e _ _

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakLeftSandwich_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M) :
    Continuous (weakLeftSandwich e a b) := by
  apply continuous_pi
  intro x
  exact (weakDualOperator_continuous e _
    ((HochschildSakai.abstract_multiplication_normal e).1 a)).comp (continuous_apply (b*x))

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakLeftSandwich_mapsTo_orbit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (a b : M) (T : M →L[ℂ] M) :
    Set.MapsTo (weakLeftSandwich e a b) (weakRightAverageOrbit e T)
      (weakRightAverageOrbit e (leftSandwichMap a b T)) := by
  apply Set.MapsTo.closure _ (weakLeftSandwich_continuous e a b)
  rintro F ⟨S, ⟨n, m, hm, rfl⟩, rfl⟩
  rw [weakLeftSandwich_image, leftSandwichMap_rightAverage]
  exact ⟨_, finiteRightAverage_mem_orbit m hm _, rfl⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
