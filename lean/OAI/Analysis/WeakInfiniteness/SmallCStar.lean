import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open TopologicalSpace

universe u v

lemma small_of_separable_metric (X : Type u) [MetricSpace X] [SeparableSpace X]
    [Nonempty X] : Small.{0} X := by
  apply small_of_injective (f := fun x : X => fun n : ℕ => dist x (denseSeq X n))
  intro x y h
  have he : (fun z : X => dist x z)=(fun z : X => dist y z) :=
    (denseRange_denseSeq X).equalizer (by fun_prop) (by fun_prop) h
  have hy := congrFun he x
  simpa only [dist_self,eq_comm,dist_eq_zero] using hy

def SmallCStarCarrier (A : Type u) [Small.{0} A] := Shrink.{0} A

section SmallTransport

variable (A : Type u) [CStarAlgebra A] [Small.{0} A]

def smallCStarEquiv : SmallCStarCarrier A ≃ A := (equivShrink A).symm

instance smallCStarNormedRing : NormedRing (SmallCStarCarrier A) := (smallCStarEquiv A).normedRing

instance smallCStarAlgebraStruct : Algebra ℂ (SmallCStarCarrier A) := (smallCStarEquiv A).algebra ℂ

instance smallCStarNormedSpace : NormedSpace ℂ (SmallCStarCarrier A) :=
  AddEquiv.normedSpace ℂ (smallCStarEquiv A).addEquiv

instance smallCStarStarRing : StarRing (SmallCStarCarrier A) := (smallCStarEquiv A).starRing

instance smallCStarStarModule : StarModule ℂ (SmallCStarCarrier A) := (smallCStarEquiv A).starModule ℂ

lemma smallCStarEquiv_isometry : Isometry (smallCStarEquiv A) := by
  intro x y
  rfl

instance smallCStarComplete : CompleteSpace (SmallCStarCarrier A) :=
  (show SmallCStarCarrier A ≃ᵢ A from
    { smallCStarEquiv A with isometry_toFun := smallCStarEquiv_isometry A }).completeSpace

instance smallCStarCStar : CStarAlgebra (SmallCStarCarrier A) where
  norm_smul_le r x := by
    change ‖smallCStarEquiv A ((smallCStarEquiv A).symm (r • smallCStarEquiv A x))‖ ≤ _
    rw [Equiv.apply_symm_apply]
    exact norm_smul_le r (smallCStarEquiv A x)
  norm_mul_self_le x := by
    change ‖smallCStarEquiv A x‖ * ‖smallCStarEquiv A x‖ ≤
      ‖smallCStarEquiv A (star x*x)‖
    change ‖smallCStarEquiv A x‖ * ‖smallCStarEquiv A x‖ ≤
      ‖smallCStarEquiv A ((smallCStarEquiv A).symm
        (smallCStarEquiv A ((smallCStarEquiv A).symm (star (smallCStarEquiv A x))) * smallCStarEquiv A x))‖
    simp only [Equiv.apply_symm_apply]
    exact CStarRing.norm_mul_self_le _

def smallCStarStarAlgEquiv : SmallCStarCarrier A ≃⋆ₐ[ℂ] A :=
  { (smallCStarEquiv A).algEquiv ℂ with
    map_smul' := fun r x => by
      change smallCStarEquiv A ((smallCStarEquiv A).symm (r • smallCStarEquiv A x))=_
      exact Equiv.apply_symm_apply _ _
    map_star' := fun x => by
      change smallCStarEquiv A ((smallCStarEquiv A).symm (star (smallCStarEquiv A x)))=_
      exact Equiv.apply_symm_apply _ _ }

end SmallTransport

end

end WeakPureInfiniteness
end

end OAI
