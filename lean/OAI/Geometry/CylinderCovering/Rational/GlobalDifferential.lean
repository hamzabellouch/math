import OAI.Geometry.CylinderCovering.Rational.GlobalTopology

namespace OAI

noncomputable section
open Set

namespace SlopeRational

theorem tiltedMap_fderiv (d s : ℝ) {p : Plane}
    (hden : radius (p 1) + d ≠ 0) :
    fderiv ℝ (tiltedMap d s) p =
      ContinuousLinearMap.id ℝ Plane + s • fderiv ℝ (field d) p := by
  have hfield := (field_contDiffAt d hden).differentiableAt (by norm_num)
  exact ((hasFDerivAt_id p).add (hfield.hasFDerivAt.const_smul s)).fderiv

private theorem matrixCLM_id_add_smul (s a b c e : ℝ) :
    ContinuousLinearMap.id ℝ Plane + s • matrixCLM a b c e =
      matrixCLM (1 + s * a) (s * b) (s * c) (1 + s * e) := by
  ext z i
  fin_cases i <;> simp [matrixCLM_apply, vec2] <;> ring

theorem tiltedMap_det (d s : ℝ) {p : Plane}
    (hden : radius (p 1) + d ≠ 0) :
    LinearMap.det (fderiv ℝ (tiltedMap d s) p).toLinearMap =
      1 + s ^ 2 * LinearMap.det (fderiv ℝ (field d) p).toLinearMap := by
  rw [tiltedMap_fderiv d s hden, field_fderiv d hden,
    matrixCLM_id_add_smul, matrixCLM_det, matrixCLM_det]
  ring

theorem tiltedMap_det_eq_one_sub_sq (d s : ℝ) {p : Plane}
    (hden : radius (p 1) + d ≠ 0) :
    LinearMap.det (fderiv ℝ (tiltedMap d s) p).toLinearMap =
      1 - (s * (d / (4 * (radius (p 1) + d) ^ 2))) ^ 2 := by
  rw [tiltedMap_det d s hden, (field_trace_det d hden).2]
  field_simp [hden]
  ring

theorem tiltedMap_det_pos {d s : ℝ} (hd : 0 < d) (hs : |s| < d)
    {p : Plane} (hp : p ∈ wedge) :
    0 < LinearMap.det (fderiv ℝ (tiltedMap d s) p).toLinearMap := by
  rw [tiltedMap_det_eq_one_sub_sq d s (denominator_pos_of_mem_wedge hd hp).ne']
  obtain ⟨hlam, hbound⟩ := eigenvalue_bound_on_wedge hd hp
  have habs : |s * (d / (4 * (radius (p 1) + d) ^ 2))| < 1 := by
    rw [abs_mul, abs_of_pos hlam]
    calc
      |s| * (d / (4 * (radius (p 1) + d) ^ 2)) ≤
          |s| * (1 / (4 * d)) := mul_le_mul_of_nonneg_left hbound (abs_nonneg s)
      _ < 1 := by
        rw [mul_one_div]
        apply (div_lt_one (by positivity : 0 < 4 * d)).2
        linarith [abs_nonneg s]
  have hsq := sq_lt_sq' (abs_lt.mp habs).1 (abs_lt.mp habs).2
  nlinarith

theorem tiltedMap_displacement_bound {d : ℝ} (hd : 0 < d) (s : ℝ)
    {p : Plane} (hp : p ∈ wedge) :
    ‖tiltedMap d s p - p‖ ≤ |s| * (3 / 8 : ℝ) := by
  simp only [tiltedMap, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (field_norm_bound hd hp) (abs_nonneg s)

theorem tiltedMap_preimage_norm_bound {d : ℝ} (hd : 0 < d) (s : ℝ)
    {p : Plane} (hp : p ∈ wedge) :
    ‖p‖ ≤ ‖tiltedMap d s p‖ + |s| * (3 / 8 : ℝ) := by
  have h := norm_sub_le (tiltedMap d s p) (tiltedMap d s p - p)
  rw [sub_sub_cancel] at h
  exact h.trans (add_le_add (le_refl _) (tiltedMap_displacement_bound hd s hp))

end SlopeRational

end

end OAI
