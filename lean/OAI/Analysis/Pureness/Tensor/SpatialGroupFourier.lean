import OAI.Analysis.Pureness.GroupAlgebra.ReducedGroupCStarAlgebra
import OAI.Analysis.Pureness.Tensor.SpatialUnitVectorSlice

namespace OAI
noncomputable section
namespace CuntzPureness
local instance spatialGroupFourierDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
open scoped TensorProduct InnerProductSpace
variable {A H G : Type*} [Group G]
variable [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def spatialGroupFourier (g : G) :=
  spatialVectorSlice (H := H) (K := GroupL2 G) α (reducedGroupAlgebra G).subtype
    (lp.single 2 g 1) groupVacuum

include hα in
theorem spatialGroupFourier_norm_le (g : G)
    (x : representedSpatialTensor (H := H) (K := GroupL2 G) α (reducedGroupAlgebra G).subtype) :
    ‖spatialGroupFourier α g x‖ ≤ ‖x‖ :=
  spatialUnitVectorSlice_norm_le (A := A) (B := reducedGroupAlgebra G)
    (H := H) (K := GroupL2 G) α hα (reducedGroupAlgebra G).subtype
    (lp.single 2 g 1) groupVacuum
    ((lp.norm_single (E := fun _ : G => ℂ)
      (by norm_num : (0 : ENNReal) < 2) g (1 : ℂ)).trans norm_one)
    (groupVacuum_norm (G := G)) x
end CuntzPureness

end

end OAI
