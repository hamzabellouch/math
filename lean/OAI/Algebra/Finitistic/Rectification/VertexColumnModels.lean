import OAI.Algebra.Finitistic.Bimodule.BimoduleVertex

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.VertexColumnModels
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
variable (N : ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ)
local notation "T" => ThreeVertexAlgebra μ
attribute [local instance] ExternalTensor.rightModule ExternalTensor.bimodule

/-- The actual vertex of an induced column is its path-corner tensor. -/
def cornerEquiv (i j : Fin 3) :
    BimoduleVertex.columnFixed μ N i j ≃ₗ[Tᵐᵒᵖ] (CornerSpaces.corner μ i j ⊗[k] N) :=
  (BimoduleVertex.columnFixedEquiv μ N i j).trans
    (CornerTensor.cornerTensorEquiv μ N i j).symm

/-- Vertices below the directed support have zero actual column component. -/
theorem reverse_zero (i j : Fin 3) (hij : i < j) :
    Subsingleton (BimoduleVertex.columnFixed μ N i j) := by
  have hc : Subsingleton (CornerSpaces.corner μ i j) :=
    ⟨fun x y => (CornerSpaces.corner_zero_of_lt μ i j hij x).trans
      (CornerSpaces.corner_zero_of_lt μ i j hij y).symm⟩
  let := hc
  have ht : ∀ x : CornerSpaces.corner μ i j ⊗[k] N, x = 0 := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul x n => simp [Subsingleton.elim x 0]
    | add x y hx hy => simp [hx,hy]
  refine ⟨fun x y => (cornerEquiv μ N i j).injective ?_⟩
  exact (ht _).trans (ht _).symm

/-- The inverse diagonal equivalence is the manuscript's original insertion e_i tensor n. -/
theorem diagonal_symm_val (i : Fin 3) (n : N) :
    ((BimoduleVertex.diagonalEquiv μ N i).symm n).val =
      ExternalTensor.columnInclusion k T N (ThreeVertexAlgebra.vertex μ i) n := by
  change (⟨(1 : k) • ThreeVertexAlgebra.vertex μ i, _⟩ :
    ExternalTensor.leftIdeal T (ThreeVertexAlgebra.vertex μ i)) ⊗ₜ[k] n =
      ExternalTensor.generator T (ThreeVertexAlgebra.vertex μ i) ⊗ₜ[k] n
  congr 1
  apply Subtype.ext
  exact one_smul k _

end LittleFinitistic.VertexColumnModels

end

end OAI
