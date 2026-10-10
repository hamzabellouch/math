import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.GroupBranchLaws

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldGroupBranchDesignation

open AllFieldHistory AllFieldHistoryChildLaws AllFieldGroupOrbitData
open AllFieldGroupNativeLaws
attribute [local instance] Classical.propDecidable Classical.decEq

def nativeBranchDesignated {K : ℕ} (w : Work K) (right : Bool)
    (side : Fin 3) (b : w.Branch) : Prop :=
  w.stage ≠ 2 ∧ AllFieldNativeCapacity.designated w.priority side
    (halfShape w.parentShape (w.splitShape b) right)

theorem sharing_iff_stage_ne_two {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) :
    sharing h = true ↔ h.val.val.1.stage ≠ 2 := by
  rcases h with ⟨⟨⟨w, phi⟩, ht⟩, ho⟩
  cases w <;> simp [sharing, Work.stage]

theorem order_branch_childWeight {K tick : ℕ} {sigma : Placement}
    (right : Bool) (h : ActiveOrder K tick sigma) (side : Fin 3)
    (b : h.val.val.1.Branch) :
    childWeight right h.val (branchShape h.val.val b) (sigma side) =
      (halfShape h.val.val.1.parentShape (h.val.val.1.splitShape b) right)
        (h.val.val.1.priority side) := by
  rw [← halfShape_childWeight, canonicalChildShape_branchShape,
    placement_symm_order_side]

theorem designated_branchShape {K tick : ℕ} {sigma : Placement}
    (right : Bool) (side : Fin 3) (h : ActiveOrder K tick sigma)
    (hside : side ≠ 0) (b : h.val.val.1.Branch) :
    AllFieldGroupOrbitData.designated right side sigma h (branchShape h.val.val b) ↔
      nativeBranchDesignated h.val.val.1 right side b := by
  change (sharing h = true ∧
    (if side = 1 then childWeight right h.val (branchShape h.val.val b) (sigma 2) = 0
      else if side = 2 then
        childWeight right h.val (branchShape h.val.val b) (sigma 0) *
          childWeight right h.val (branchShape h.val.val b) (sigma 1) = 0
      else False)) ↔ _
  rw [sharing_iff_stage_ne_two]
  simp only [order_branch_childWeight, nativeBranchDesignated,
    AllFieldNativeCapacity.designated]
  fin_cases side
  · exact False.elim (hside rfl)
  · simp
  · simp

end MatrixMultiplication.AllFieldGroupBranchDesignation

end

end MatrixAllFields

end OAI
