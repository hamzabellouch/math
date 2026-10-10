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

namespace WeakPureInfiniteness

universe u v

instance uliftStarRing {A : Type u} [Semiring A] [StarRing A] : StarRing (ULift.{v} A) where
  star x := ⟨star x.down⟩
  star_involutive x := by cases x; simp only [star_star]
  star_mul x y := by apply ULift.down_injective; exact star_mul x.down y.down
  star_add x y := by apply ULift.down_injective; exact star_add x.down y.down

instance uliftStarModule {A : Type u} [Semiring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] : StarModule ℂ (ULift.{v} A) where
  star_smul r x := by apply ULift.down_injective; exact star_smul r x.down

instance uliftCStarAlgebra {A : Type u} [CStarAlgebra A] : CStarAlgebra (ULift.{v} A) where
  norm_mul_self_le x := CStarRing.norm_mul_self_le x.down

def uliftStarAlgEquiv {A : Type u} [CStarAlgebra A] : ULift.{v} A ≃⋆ₐ[ℂ] A :=
  { ULift.algEquiv (R := ℂ) (A := A) with
    map_smul' := fun _ _ => rfl
    map_star' := fun _ => rfl }

end WeakPureInfiniteness
end

end OAI
