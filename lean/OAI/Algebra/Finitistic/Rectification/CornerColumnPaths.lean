import OAI.Algebra.Finitistic.Rectification.CornerColumnComplex

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.CornerColumnPaths
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
local notation "T" => ThreeVertexAlgebra μ
attribute [local instance] ExternalTensor.rightModule ExternalTensor.bimodule

/-- Right multiplication by the original path on the actual vertex corner. -/
def cornerMap (v i j : Fin 3) (a : ThreeVertexAlgebra μ)
    (ha : a * ThreeVertexAlgebra.vertex μ i = a) :
    CornerSpaces.corner μ v j →ₗ[k] CornerSpaces.corner μ v i where
  toFun x := ⟨x.val*a,by
    change ThreeVertexAlgebra.vertex μ v * (x.val*a) * ThreeVertexAlgebra.vertex μ i = x.val*a
    calc
      _ = (ThreeVertexAlgebra.vertex μ v * x.val) *
        (a * ThreeVertexAlgebra.vertex μ i) := by simp only [mul_assoc]
      _ = x.val*a := by rw [CornerProjection.corner_left_fixed,ha]⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' c x := Subtype.ext (smul_mul_assoc _ _ _)

/-- The corner-tensor identification carries the actual induced path map to right multiplication. -/
theorem path_naturality (v i j : Fin 3) (a : ThreeVertexAlgebra μ)
    (ha : a * ThreeVertexAlgebra.vertex μ i = a)
    (D : CochainComplex (ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ) ℤ) :
    TensorComplex.complexMap D (ModuleCat.ofHom (cornerMap μ v i j a ha)) ≫
        (CornerColumnComplex.complexIso μ v i D).hom =
      (CornerColumnComplex.complexIso μ v j D).hom ≫
        ((BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex μ v)).mapHomologicalComplex (.up ℤ)).map
          (ExternalTensor.Section4.path k T (ThreeVertexAlgebra.vertex μ i)
            (ThreeVertexAlgebra.vertex μ j) a ha D) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul c z => rfl
  | add x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

end LittleFinitistic.CornerColumnPaths

end

end OAI
