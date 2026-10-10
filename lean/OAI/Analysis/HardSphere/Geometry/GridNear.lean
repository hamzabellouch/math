import Mathlib
import OAI.Analysis.HardSphere.Geometry.GridAlignment

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
namespace HardSphere.Groups
open HardSphere.Lattice HardSphere.CellOrbital
attribute [local instance] Classical.propDecidable
lemma grid_near_of_distance {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (v w : Fin 3→Fin K) (h : torusDistance L (gridCenter L v) (gridCenter L w)≤23) :
    torusNear K 24 (gridSite w) (gridSite v) := by
  obtain ⟨z,hz,he⟩ := grid_packing_witness L hL (fun j ↦ ((w j).val:ℝ)) v
    (fun j ↦ (dist_coord_le_torusDistance L (gridCenter L v) (gridCenter L w) j).trans h)
  refine ⟨fun j ↦ z j-(w j).val,?_,?_⟩
  · intro j
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hz
    have hl' := hl j
    have hu' := hu j
    simp only [Int.floor_natCast] at hl' hu'
    change |z j-(w j).val|≤24
    exact abs_le.mpr ⟨by omega,by omega⟩
  · intro j
    have hj := congrFun he j
    dsimp [torusProjection,gridSite] at hj ⊢
    push_cast
    rw [←hj]
    ring
lemma distance_far_of_grid_far {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    {R : ℕ} (hR : 24≤R) (v w : Fin 3→Fin K)
    (h : ¬torusNear K R (gridSite v) (gridSite w)) :
    23<torusDistance L (gridCenter L v) (gridCenter L w) := by
  by_contra hn
  apply h
  exact torusNear_mono hR (torusNear_symm (grid_near_of_distance L hL v w (le_of_not_gt hn)))

end HardSphere.Groups

end
end

end

end OAI
