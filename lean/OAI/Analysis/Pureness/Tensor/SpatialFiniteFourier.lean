import OAI.Analysis.Pureness.Operators.FiniteCoordinateReconstruction
import OAI.Analysis.Pureness.Tensor.SpatialFourierCoefficients
import OAI.Analysis.Pureness.Tensor.SpatialTensorContinuousLegs

namespace OAI
noncomputable section
namespace CuntzPureness
local instance spatialFiniteFourierDecidableEq {X : Type*} : DecidableEq X :=
  Classical.decEq X
open scoped TensorProduct
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def spatialFiniteFourier (s : Finset G) (c : G → ℂ) :
    representedSpatialTensor α (reducedGroupAlgebra G).subtype →L[ℂ]
      representedSpatialTensor α (reducedGroupAlgebra G).subtype :=
  finiteCoordinateReconstruction
    (fun g => spatialTensorLeftLeg α (reducedGroupAlgebra G).subtype
      (reducedGroupUnitary G g : reducedGroupAlgebra G)) (spatialGroupFourier α) s c

lemma spatialFiniteFourier_apply (s : Finset G) (c : G → ℂ)
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    spatialFiniteFourier (G := G) α s c x = ∑ g ∈ s,
      spatialCompletionMap α (reducedGroupAlgebra G).subtype
        ((c g • spatialGroupFourier α g x) ⊗ₜ[ℂ]
          (reducedGroupUnitary G g : reducedGroupAlgebra G)) := by
  exact finiteCoordinateReconstruction_apply _ _ s c x

include hα in
lemma spatialFiniteFourier_generator (s : Finset G) (c : G → ℂ) (a : A) (g : G) :
    spatialFiniteFourier (G := G) α s c (spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (a ⊗ₜ[ℂ] (reducedGroupUnitary G g : reducedGroupAlgebra G))) =
      (if g ∈ s then c g else 0) •
        spatialCompletionMap α (reducedGroupAlgebra G).subtype
          (a ⊗ₜ[ℂ] (reducedGroupUnitary G g : reducedGroupAlgebra G)) := by
  exact finiteCoordinateReconstruction_generator (A := A)
    (E := representedSpatialTensor α (reducedGroupAlgebra G).subtype) (G := G) _ _
    (fun g h a => spatialGroupFourier_generator α hα g h a) s c a g

include hα in

lemma spatialFiniteFourier_norm_le (s : Finset G) (c : G → ℂ)
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    ‖spatialFiniteFourier (G := G) α s c x‖ ≤ (∑ g ∈ s, ‖c g‖) * ‖x‖ := by
  apply finiteCoordinateReconstruction_norm_le (A := A)
    (E := representedSpatialTensor α (reducedGroupAlgebra G).subtype) (G := G) _ _ _
    (fun g x => spatialGroupFourier_norm_le α hα g x) s c x
  intro g a
  have hu : ‖(reducedGroupUnitary G g : reducedGroupAlgebra G)‖ ≤ 1 := by
    change ‖groupLeft g‖ ≤ 1
    exact (groupL2Perm (Equiv.mulLeft g)).toLinearIsometry.norm_toContinuousLinearMap_le
  exact (spatialCompletionMap_tmul_norm_le α (reducedGroupAlgebra G).subtype a _).trans
    ((mul_le_mul_of_nonneg_left hu (norm_nonneg a)).trans_eq (mul_one _))
end CuntzPureness

end

end OAI
