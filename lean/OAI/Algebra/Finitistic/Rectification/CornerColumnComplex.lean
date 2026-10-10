import OAI.Algebra.Finitistic.Rectification.VertexColumnComplex
import OAI.Algebra.Finitistic.Rectification.TensorComplex

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.CornerColumnComplex
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
local notation "T" => ThreeVertexAlgebra μ
attribute [local instance] ExternalTensor.rightModule ExternalTensor.bimodule

/-- Embed an actual corner into the principal left ideal of its source vertex. -/
def cornerToIdeal (i j : Fin 3) : CornerSpaces.corner μ i j →ₗ[k]
    ExternalTensor.leftIdeal T (ThreeVertexAlgebra.vertex μ j) where
  toFun x := ⟨x.val,⟨x.val,CornerProjection.corner_right_fixed μ i j x⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The corner equivalence retains the actual tensor insertion on pure tensors. -/
theorem corner_symm_tmul_val (N : ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ)
    (i j : Fin 3) (x : CornerSpaces.corner μ i j) (n : N) :
    ((VertexColumnModels.cornerEquiv μ N i j).symm (x ⊗ₜ[k] n)).val =
      cornerToIdeal μ i j x ⊗ₜ[k] n := by
  rfl

/-- Every actual vertex column is its concrete corner-tensor complex. -/
def complexIso (i j : Fin 3)
    (D : CochainComplex (ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ) ℤ) :
    TensorComplex.complex D (ModuleCat.of k (CornerSpaces.corner μ i j)) ≅
      ((VertexColumnComplex.vertexColumn μ i j).mapHomologicalComplex (.up ℤ)).obj D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (VertexColumnModels.cornerEquiv μ (D.X n) i j).symm.toModuleIso) (by
      intro n m hnm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul c v => rfl
      | add x y hx hy =>
        exact (map_add _ _ _).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm))
end LittleFinitistic.CornerColumnComplex

end

end OAI
