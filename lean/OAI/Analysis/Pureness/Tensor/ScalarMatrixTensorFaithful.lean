import OAI.Analysis.Pureness.Tensor.ScalarMatrixTensor
import OAI.Analysis.Pureness.Tensor.CommutingTensorInjective

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped TensorProduct
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A))
variable (hy : y ≠ 0) (f : StateSpace y) (U : Ultrafilter ℕ)

theorem matrixStateScalarTensorHom_injective :
    Function.Injective (matrixStateScalarTensorHom hsimple y hy f U) :=
  commutingStarTensorHom_injective hsimple
    (matrixStateDiagonalAWEmbedding hsimple y hy f U)
    (scalarTracialMatrixAWEmbedding hsimple y hy f U)
    (scalarTracialMatrixAWEmbedding_injective hsimple y hy f U)
    (scalarTracialMatrixAWEmbedding_commute hsimple y hy f U)

theorem matrixStateScalarTensorHom_eq_zero_iff
    (z : A ⊗[ℂ] ScalarTracialMatrixUltraproduct U) :
    matrixStateScalarTensorHom hsimple y hy f U z=0 ↔ z=0 :=
  map_eq_zero_iff _ (matrixStateScalarTensorHom_injective hsimple y hy f U)

theorem matrixStateScalarTensorHom_norm_pos
    (z : A ⊗[ℂ] ScalarTracialMatrixUltraproduct U) (hz : z ≠ 0) :
    0 < ‖matrixStateScalarTensorHom hsimple y hy f U z‖ :=
  norm_pos_iff.mpr (fun h => hz ((matrixStateScalarTensorHom_eq_zero_iff hsimple y hy f U z).mp h))
end CuntzPureness

end

end OAI
