import OAI.Combinatorics.Crossing.LocalLineBends

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segment_direction_of_local_line_at_interior (a b x d : Plane)
    (hx : x ∈ openSegmentTrace a b) (U : Set Plane) (hU : IsOpen U) (hxU : x ∈ U)
    (hline : ∀ z ∈ U, z ∈ segment ℝ a b → det2 d (z-x)=0) :
    det2 d (b-a)=0 := by
  obtain ⟨t,ht,he⟩ := hx
  have hxseg : x ∈ segment ℝ a b := by
    rw [← Path.range_segment]
    exact ⟨⟨t,⟨ht.1.le,ht.2.le⟩⟩,by simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he⟩
  have hsub := (convex_segment (𝕜 := ℝ) a b).segment_subset hxseg (right_mem_segment ℝ a b)
  have hh := segment_direction_of_local_line b x d U hU hxU (fun z hz hs => hline z hz (hsub hs))
  have heq : b-x=(1-t) • (b-a) := by
    rw [← he]
    apply Prod.ext <;> dsimp [segmentPoint] <;> ring
  rw [heq,det2_smul_right] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by linarith [ht.2])

theorem det2_ne_zero_of_parallel_nonzero (d e u v : Plane)
    (hde : det2 d e ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hdu : det2 d u=0) (hev : det2 e v=0) : det2 u v ≠ 0 := by
  have hd : d ≠ 0 := by intro h; subst d; simp at hde
  have he : e ≠ 0 := by intro h; subst e; simp at hde
  have hU := vector_parallel_of_det_zero d u hd hdu
  have hV := vector_parallel_of_det_zero e v he hev
  have hα : dot2 d u/squaredLength d ≠ 0 := by
    intro h
    rw [h,zero_smul] at hU
    exact hu hU
  have hβ : dot2 e v/squaredLength e ≠ 0 := by
    intro h
    rw [h,zero_smul] at hV
    exact hv hV
  conv_lhs => rw [hU,hV,det2_smul_left,det2_smul_right]
  exact mul_ne_zero hα (mul_ne_zero hβ hde)

end Zarankiewicz

end

end OAI
