import OAI.GroupTheory.PolycyclicRecognition.Finiteness.TensorProjectiveTower
import Mathlib.Algebra.Algebra.Bilinear

namespace OAI

/-! # Unit and multiplication on the small coefficient tensor functor -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

abbrev smallCoefficientTensor (A : Rep.{0} ℤ G) : Rep ℤ G :=
  smallCoefficientRepresentation G ⊗ A

def smallCoefficientTensorUnit (A : Rep.{0} ℤ G) : A ⟶ smallCoefficientTensor A :=
  Rep.ofHom ⟨TensorProduct.mk ℤ (SmallCoefficientRing G) A 1, fun g => by
      apply LinearMap.ext
      intro x
      change (1 : SmallCoefficientRing G) ⊗ₜ[ℤ] A.ρ g x =
        (g • (1 : SmallCoefficientRing G)) ⊗ₜ[ℤ] A.ρ g x
      rw [smul_one]⟩

@[simp]
theorem smallCoefficientTensorUnit_apply (A : Rep.{0} ℤ G) (x : A) :
    (smallCoefficientTensorUnit A).hom x = (1 : SmallCoefficientRing G) ⊗ₜ[ℤ] x := rfl

theorem smallCoefficientTensorUnit_natural {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    f ≫ smallCoefficientTensorUnit B =
      smallCoefficientTensorUnit A ≫ (tensorLeft (smallCoefficientRepresentation G)).map f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

def smallCoefficientMultiplication :
    smallCoefficientRepresentation G ⊗ smallCoefficientRepresentation G ⟶
      smallCoefficientRepresentation G :=
  Rep.ofHom ⟨LinearMap.mul' ℤ (SmallCoefficientRing G), fun g => by
    apply TensorProduct.ext'
    intro x y
    change (g • x) * (g • y) = g • (x * y)
    exact (smul_mul' g x y).symm⟩

def smallCoefficientTensorMultiply (A : Rep.{0} ℤ G) :
    smallCoefficientTensor (smallCoefficientTensor A) ⟶ smallCoefficientTensor A :=
  (α_ (smallCoefficientRepresentation G) (smallCoefficientRepresentation G) A).inv ≫
    (smallCoefficientMultiplication ⊗ₘ 𝟙 A)

@[simp]
theorem smallCoefficientTensorMultiply_apply (A : Rep.{0} ℤ G)
    (b c : SmallCoefficientRing G) (x : A) :
    (smallCoefficientTensorMultiply A).hom (b ⊗ₜ[ℤ] (c ⊗ₜ[ℤ] x)) =
      (b * c) ⊗ₜ[ℤ] x := rfl

theorem smallCoefficientTensorMultiply_unit (A : Rep.{0} ℤ G) :
    smallCoefficientTensorUnit (smallCoefficientTensor A) ≫
      smallCoefficientTensorMultiply A = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro b x
  change (1 * b) ⊗ₜ[ℤ] x = b ⊗ₜ[ℤ] x
  rw [one_mul]

theorem smallCoefficientTensorMultiply_map_unit (A : Rep.{0} ℤ G) :
    (tensorLeft (smallCoefficientRepresentation G)).map (smallCoefficientTensorUnit A) ≫
      smallCoefficientTensorMultiply A = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro b x
  change (b * 1) ⊗ₜ[ℤ] x = b ⊗ₜ[ℤ] x
  rw [mul_one]

theorem smallCoefficientTensorMultiply_natural {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    (tensorLeft (smallCoefficientRepresentation G)).map
        ((tensorLeft (smallCoefficientRepresentation G)).map f) ≫
        smallCoefficientTensorMultiply B =
      smallCoefficientTensorMultiply A ≫
        (tensorLeft (smallCoefficientRepresentation G)).map f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro b
  apply TensorProduct.ext'
  intro c x
  rfl

/-- Extend a primitive using ring multiplication and cancel its epimorphic cover. -/
theorem smallCoefficientTensor_split_of_unit_homotopy {P Q K : Rep.{0} ℤ G}
    (π : Q ⟶ K) [Epi π] (ι : K ⟶ P) (r : P ⟶ smallCoefficientTensor K)
    (hr : (π ≫ ι) ≫ r = π ≫ smallCoefficientTensorUnit K) :
    (tensorLeft (smallCoefficientRepresentation G)).map ι ≫
      ((tensorLeft (smallCoefficientRepresentation G)).map r ≫
        smallCoefficientTensorMultiply K) = 𝟙 _ := by
  let F := tensorLeft (smallCoefficientRepresentation G)
  apply (cancel_epi (F.map π)).mp
  have h := congrArg (fun f => F.map f ≫ smallCoefficientTensorMultiply K) hr
  dsimp only [F] at h ⊢
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc,
    smallCoefficientTensorMultiply_map_unit, Category.comp_id] using h

end PolycyclicRecognition

end

end OAI
