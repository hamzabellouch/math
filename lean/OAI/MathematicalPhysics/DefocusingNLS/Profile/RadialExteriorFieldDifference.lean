import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorErrorField

namespace OAI

/-! Quantitative comparison with the linear exterior error field. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def radialExteriorMatrixDifference (ν μ : ℂ) : ℝ :=
  ‖(2*ν+10)-(2*μ+10)‖+‖ν*(ν+10)-μ*(μ+10)‖

theorem radialExteriorErrorMatrix_difference (ν μ : ℂ) (z : ℂ × ℂ) :
    ‖radialExteriorErrorMatrix ν z-radialExteriorErrorMatrix μ z‖ ≤
      radialExteriorMatrixDifference ν μ*‖z‖ := by
  have he : radialExteriorErrorMatrix ν z-radialExteriorErrorMatrix μ z =
      (0,-(((2*ν+10)-(2*μ+10))*z.2+(ν*(ν+10)-μ*(μ+10))*z.1)) := by
    apply Prod.ext
    · simp [radialExteriorErrorMatrix]
    · change -((2*ν+10)*z.2+(ν*(ν+10))*z.1)-
        (-((2*μ+10)*z.2+(μ*(μ+10))*z.1))=_
      ring
  rw [he,Prod.norm_def,norm_zero,norm_neg,max_eq_right (norm_nonneg _)]
  calc
    _ ≤ ‖((2*ν+10)-(2*μ+10))*z.2‖+‖(ν*(ν+10)-μ*(μ+10))*z.1‖ := norm_add_le _ _
    _ = ‖(2*ν+10)-(2*μ+10)‖*‖z.2‖+‖ν*(ν+10)-μ*(μ+10)‖*‖z.1‖ := by rw [norm_mul,norm_mul]
    _ ≤ ‖(2*ν+10)-(2*μ+10)‖*‖z‖+‖ν*(ν+10)-μ*(μ+10)‖*‖z‖ := by
      gcongr
      · exact norm_snd_le z
      · exact norm_fst_le z
    _ = _ := by unfold radialExteriorMatrixDifference; ring

theorem radialExteriorErrorField_linear_difference (κ L : ℝ) (ν μ : ℂ)
    (N : ℂ → ℂ) (hLip : ∀ z w, ‖N z-N w‖ ≤ L*‖z-w‖) (f : ℝ → ℂ)
    (r s : ℝ →ᵇ ℂ × ℂ) (t : ℝ) (z : ℂ × ℂ) :
    ‖radialExteriorErrorField κ ν N f r t z-(radialExteriorErrorMatrix μ z+s t)‖ ≤
      (radialExteriorMatrixDifference ν μ+L)*‖z‖+‖r-s‖ := by
  have hL : 0 ≤ L := by
    have h := hLip 1 0
    simp only [sub_zero,norm_one,mul_one] at h
    exact (norm_nonneg _).trans h
  have hinc : ‖radialExteriorWeightedIncrement κ N f t z.1‖ ≤ L*‖z‖ := by
    have hb := radialExteriorWeightedIncrement_difference κ L N hLip f t z.1 0
    simp only [radialExteriorWeightedIncrement,mul_zero,add_zero,sub_self,mul_zero,sub_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (norm_fst_le z) hL)
  have he : radialExteriorErrorField κ ν N f r t z-(radialExteriorErrorMatrix μ z+s t) =
      (radialExteriorErrorMatrix ν z-radialExteriorErrorMatrix μ z)+
        (0,radialExteriorWeightedIncrement κ N f t z.1)+(r t-s t) := by
    unfold radialExteriorErrorField
    abel
  rw [he]
  calc
    _ ≤ ‖radialExteriorErrorMatrix ν z-radialExteriorErrorMatrix μ z‖+
        ‖(0,radialExteriorWeightedIncrement κ N f t z.1)‖+‖r t-s t‖ := @norm_add₃_le _ _ _ _ _
    _ ≤ radialExteriorMatrixDifference ν μ*‖z‖+L*‖z‖+‖r-s‖ := by
      apply add_le_add
      · apply add_le_add (radialExteriorErrorMatrix_difference ν μ z)
        simpa only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using hinc
      · exact (r-s).norm_coe_le_norm t
    _ = _ := by ring

end DefocusingNLS

end OAI
