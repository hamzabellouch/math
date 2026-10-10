import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # Uniform continuity of quadratic coefficients near a unit vector -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem vector_quadratic_sub_le (T : H →L[ℂ] H) (v w : H) :
    ‖inner ℂ v (T v)-inner ℂ w (T w)‖ ≤ ‖T‖*(‖v‖+‖w‖)*‖v-w‖ := by
  have he : inner ℂ v (T v)-inner ℂ w (T w) =
      inner ℂ (v-w) (T v)+inner ℂ w (T (v-w)) := by
    rw [inner_sub_left,map_sub,inner_sub_right]
    abel
  rw [he]
  calc
    _ ≤ ‖inner ℂ (v-w) (T v)‖+‖inner ℂ w (T (v-w))‖ := norm_add_le _ _
    _ ≤ ‖v-w‖*‖T v‖+‖w‖*‖T (v-w)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖v-w‖*(‖T‖*‖v‖)+‖w‖*(‖T‖*‖v-w‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (T.le_opNorm (v-w)) (norm_nonneg _))
    _ = _ := by ring

theorem vector_quadratic_error_le_of_unit (T : H →L[ℂ] H) (v w : H)
    (hw : ‖w‖=1) {ε : ℝ} (hε : ε ≤ 1) (hv : ‖v-w‖ ≤ ε) :
    ‖inner ℂ v (T v)-inner ℂ w (T w)‖ ≤ 3*‖T‖*ε := by
  have hvnorm : ‖v‖ ≤ 2 := by
    have hh := norm_le_norm_sub_add v w
    rw [hw] at hh
    linarith
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hv
  calc
    _ ≤ ‖T‖*(‖v‖+‖w‖)*‖v-w‖ := vector_quadratic_sub_le T v w
    _ ≤ ‖T‖*(2+1)*ε := by
      rw [hw]
      gcongr
    _ = _ := by ring

theorem vector_quadratic_gt_of_near_unit (T : H →L[ℂ] H) (v w : H)
    (hw : ‖w‖=1) {ε c c' : ℝ} (hε : ε ≤ 1) (hv : ‖v-w‖ ≤ ε)
    (hc : c' < (inner ℂ w (T w)).re) (hsmall : 3*‖T‖*ε < c'-c) :
    c < (inner ℂ v (T v)).re := by
  have hh := vector_quadratic_error_le_of_unit T v w hw hε hv
  have hr : |(inner ℂ v (T v)).re-(inner ℂ w (T w)).re| ≤ 3*‖T‖*ε := by
    have hb := (Complex.abs_re_le_norm (inner ℂ v (T v)-inner ℂ w (T w))).trans hh
    exact hb
  have hlow := (abs_le.mp hr).1
  linarith

end

end KadisonKastler

end OAI
