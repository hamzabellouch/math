import OAI.Analysis.Pureness.GroupAlgebra.ReducedGroupCStarAlgebra

namespace OAI
noncomputable section
namespace CuntzPureness
local instance reducedGroupMatrixCoefficientsDecidableEq {X : Type*} :
    DecidableEq X := Classical.decEq X
open scoped InnerProductSpace
variable {G : Type*} [Group G]

omit [Group G] in
lemma group_delta_inner (g : G) (x : GroupL2 G) :
    ⟪(lp.single 2 g 1 : GroupL2 G), x⟫_ℂ = x g := by
  simp [lp.inner_single_left]

theorem reducedGroup_matrix_coefficient (a : reducedGroupAlgebra G) (g h : G) :
    ⟪(lp.single 2 g 1 : GroupL2 G), (a : GroupOperator G) (lp.single 2 h 1)⟫_ℂ =
      ⟪(lp.single 2 (g * h⁻¹) 1 : GroupL2 G), (a : GroupOperator G) groupVacuum⟫_ℂ := by
  rw [group_delta_inner, group_delta_inner]
  have hd : (lp.single 2 h 1 : GroupL2 G) = groupRight h⁻¹ groupVacuum := by
    rw [groupRight_vacuum, inv_inv]
  rw [hd]
  have hc := congrArg (fun S : GroupOperator G => S groupVacuum)
    (reducedGroup_commute_right G a h⁻¹).eq
  change (a : GroupOperator G) (groupRight h⁻¹ groupVacuum) =
    groupRight h⁻¹ ((a : GroupOperator G) groupVacuum) at hc
  rw [hc, groupRight_apply]
end CuntzPureness

end

end OAI
