import OAI.Geometry.CylinderCovering.Convexity.NormalFrame
import OAI.Geometry.TriangularCovering.Main

namespace OAI

noncomputable section
open scoped InnerProductSpace
namespace CylinderNormalFrame

theorem shadowArea_eq_frameCost (u : Space) (hu : ‖u‖ = 1) :
    TriangularCovering.shadowArea u = frameCost u := by
  rw [TriangularCovering.shadowArea_abs_sum hu]
  unfold frameCost
  simp only [Fin.sum_univ_four]
  rw [inner_normal_zero, inner_normal_one, inner_normal_two, inner_normal_three]
  simp [TriangularCovering.inner_coord, TriangularCovering.faceNormal,
    TriangularCovering.H, abs_div, abs_of_nonneg (Real.sqrt_nonneg (3 : ℝ))]
  have h3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  ring_nf

theorem geometric_shadow_lower_bound (u : Space) (hu : ‖u‖ = 1) :
    Real.sqrt 2 ≤ TriangularCovering.shadowArea u := by
  rw [shadowArea_eq_frameCost u hu]
  exact frameCost_lower_bound u hu

theorem geometric_projection_minimum : TriangularCovering.A_min = Real.sqrt 2 := by
  unfold TriangularCovering.A_min
  apply le_antisymm
  · apply csInf_le
    · exact ⟨Real.sqrt 2, by
        rintro a ⟨u, hu, rfl⟩
        exact geometric_shadow_lower_bound u hu⟩
    · exact ⟨edgeDirection, edgeDirection_unit,
        (shadowArea_eq_frameCost edgeDirection edgeDirection_unit).trans
          frameCost_edgeDirection |>.symm⟩
  · apply le_csInf
    · exact ⟨Real.sqrt 2, edgeDirection, edgeDirection_unit,
        (shadowArea_eq_frameCost edgeDirection edgeDirection_unit).trans
          frameCost_edgeDirection |>.symm⟩
    · rintro a ⟨u, hu, rfl⟩
      exact geometric_shadow_lower_bound u hu

end CylinderNormalFrame

end

end OAI
