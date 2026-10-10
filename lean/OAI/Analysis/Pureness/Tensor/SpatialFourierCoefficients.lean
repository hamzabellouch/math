import OAI.Analysis.Pureness.Tensor.SpatialGroupFourier

namespace OAI
noncomputable section
namespace CuntzPureness
local instance spatialFourierCoefficientsDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
open scoped TensorProduct InnerProductSpace
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

include hα in
lemma spatialGroupFourier_tensor (g : G) (z : A ⊗[ℂ] reducedGroupAlgebra G) :
    spatialGroupFourier α g (spatialCompletionMap α (reducedGroupAlgebra G).subtype z) =
      algebraicSpatialSlice (reducedGroupAlgebra G).subtype (lp.single 2 g 1) groupVacuum z :=
  spatialVectorSlice_tensor α hα (reducedGroupAlgebra G).subtype
    (lp.single 2 g 1) groupVacuum z

lemma group_delta_inner_translation (g h : G) :
    ⟪(lp.single 2 g 1 : GroupL2 G), groupLeft h groupVacuum⟫_ℂ =
      if g = h then 1 else 0 := by
  classical
  rw [groupLeft_vacuum, lp.inner_single_left]
  simp [lp.single_apply, Pi.single_apply]

include hα in
lemma spatialGroupFourier_generator (g h : G) (a : A) :
    spatialGroupFourier α g (spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (a ⊗ₜ[ℂ] (reducedGroupUnitary G h : reducedGroupAlgebra G))) =
        if g = h then a else 0 := by
  classical
  rw [spatialGroupFourier_tensor α hα, algebraicSpatialSlice_tmul]
  change (⟪(lp.single 2 g 1 : GroupL2 G), groupLeft h groupVacuum⟫_ℂ) • a = _
  rw [group_delta_inner_translation]
  split_ifs <;> simp

include hα in
lemma spatialGroupFourier_polynomial (g : G) (s : Finset G) (a : G → A) :
    spatialGroupFourier α g (∑ h ∈ s,
      spatialCompletionMap α (reducedGroupAlgebra G).subtype
        (a h ⊗ₜ[ℂ] (reducedGroupUnitary G h : reducedGroupAlgebra G))) =
      if g ∈ s then a g else 0 := by
  classical
  simp only [map_sum, spatialGroupFourier_generator α hα]
  simp
end CuntzPureness

end

end OAI
