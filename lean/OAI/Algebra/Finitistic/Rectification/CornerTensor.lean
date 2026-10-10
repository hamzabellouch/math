import OAI.Algebra.Finitistic.Rectification.CornerProjection
import OAI.Algebra.Finitistic.Rectification.TensorProjection

namespace OAI
noncomputable section
open scoped TensorProduct

namespace LittleFinitistic.CornerTensor
open ThreeVertexAlgebra CornerSpaces CornerProjection TensorProjection
attribute [local instance] ExternalTensor.rightModule ExternalTensor.bimodule
universe u v
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
variable (N : Type v) [AddCommGroup N] [Module k N]
  [Module (ThreeVertexAlgebra μ)ᵐᵒᵖ N] [IsScalarTower k (ThreeVertexAlgebra μ)ᵐᵒᵖ N]

/-- The concrete corner tensor is the fixed submodule of the induced column. -/
def cornerTensorEquiv (i j : Fin 3) :
    (corner μ i j ⊗[k] N) ≃ₗ[(ThreeVertexAlgebra μ)ᵐᵒᵖ]
    TensorProjection.fixed (B := ThreeVertexAlgebra μ) (N := N) (projection μ i j) :=
  (rightCongr (B := ThreeVertexAlgebra μ) (N := N) (rangeEquiv μ i j).symm).trans
    (imageTensorEquiv (B := ThreeVertexAlgebra μ) (N := N)
      (projection μ i j) (projection_idempotent μ i j))

/-- This fixed-space definition uses the original left vertex action on the column. -/
theorem fixed_iff_left_action (i j : Fin 3)
    (x : ExternalTensor.Column k (ThreeVertexAlgebra μ) N (vertex μ j)) :
    x ∈ TensorProjection.fixed (B := ThreeVertexAlgebra μ) (projection μ i j) ↔
      vertex μ i • x = x := by
  rw [TensorProjection.mem_fixed]
  have h : rightMap (B := ThreeVertexAlgebra μ) (projection μ i j) x = vertex μ i • x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n => rfl
    | add x y hx hy => simp_all [smul_add]
  rw [h]

/-- Scalar tensor multiplication is right B-linear with the actual external action. -/
def scalarTensorEquiv : (k ⊗[k] N) ≃ₗ[(ThreeVertexAlgebra μ)ᵐᵒᵖ] N where
  __ := (TensorProduct.lid k N).toAddEquiv
  map_smul' c x := by
    induction x using TensorProduct.inductionOn with
    | tmul r n =>
      change r • (c • n) = c • (r • n)
      exact smul_comm r c n
    | add x y hx hy => simp_all [smul_add]

/-- The diagonal vertex component of its own induced column is exactly N. -/
def diagonalColumnEquiv (i : Fin 3) :
    TensorProjection.fixed (B := ThreeVertexAlgebra μ) (N := N) (projection μ i i)
      ≃ₗ[(ThreeVertexAlgebra μ)ᵐᵒᵖ] N :=
  (cornerTensorEquiv μ N i i).symm.trans
    ((rightCongr (B := ThreeVertexAlgebra μ) (N := N) (diagonalEquiv μ i)).trans
      (scalarTensorEquiv μ N))
end LittleFinitistic.CornerTensor

end

end OAI
