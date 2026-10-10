import OAI.MeasureTheory.Falconer.Angular.AngularChart

namespace OAI

/-!
# The failed perpendicular test in an actual spherical chart

The normalized affine chart stays within twice its tangent displacement
of the cap center. Its coordinate derivative therefore inherits the
uniform lower bound proved for the tangential sphere field.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_normalization_sub_le {w z : E} (hw : ‖w‖ = 1) (hz : z ≠ 0) :
    ‖‖z‖⁻¹ • z - w‖ ≤ 2*‖z-w‖ := by
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have he : ‖z‖⁻¹ • z - w = (z-w) + (‖z‖⁻¹-1) • z := by module
  have hnorm : ‖(‖z‖⁻¹-1) • z‖ = |‖z‖-1| := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ = |(‖z‖⁻¹-1)*‖z‖| := by rw [abs_mul,abs_of_nonneg (norm_nonneg z)]
      _ = |1-‖z‖| := by rw [sub_mul,inv_mul_cancel₀ hzn,one_mul]
      _ = _ := abs_sub_comm _ _
  rw [he]
  calc
    _ ≤ ‖z-w‖ + ‖(‖z‖⁻¹-1) • z‖ := norm_add_le _ _
    _ = ‖z-w‖ + |‖z‖-1| := by rw [hnorm]
    _ ≤ ‖z-w‖ + ‖z-w‖ := by
      exact add_le_add le_rfl (by simpa only [hw] using abs_norm_sub_norm_le z w)
    _ = _ := by ring

theorem tangent_chart_nonzero {w h : E} (hw : ‖w‖ = 1) (hh : inner ℝ w h = 0) :
    w+h ≠ 0 := by
  intro he
  have hi := congrArg (inner ℝ w) he
  simp only [inner_add_right,real_inner_self_eq_norm_sq,hw,one_pow,hh,add_zero,
    inner_zero_right] at hi
  norm_num at hi

/-- A single coordinate direction works for every allowed point and
direction replacement in the discarded cell--cap term. -/
theorem perpendicular_failure_chart_nonstationary {w₀ d : E}
    (hw₀ : ‖w₀‖ = 1) {τ : ℝ} (hτ : 0 < τ)
    (hbad : τ < ‖perpendicularPart w₀ d‖) :
    ∃ t : E, ‖t‖ = 1 ∧ inner ℝ w₀ t = 0 ∧
      ∀ (y v : E) (u : ℝ), inner ℝ w₀ y = 0 → ‖y+u•t‖ ≤ 1 →
        ‖v-d‖ + 4*‖y+u•t‖*‖d‖ ≤ τ/2 →
        τ/4 ≤ |deriv (fun x => inner ℝ (normalizedLine (w₀+y) t x) v) u| := by
  obtain ⟨t,ht,htan,hfield⟩ := perpendicular_failure_nonstationary hw₀ hτ hbad
  refine ⟨t,ht,htan,?_⟩
  intro y v u hy hsmall herr
  have hh : inner ℝ w₀ (y+u•t) = 0 := by
    simp only [inner_add_right,real_inner_smul_right,hy,htan,mul_zero,add_zero]
  have hne : (w₀+y)+u•t ≠ 0 := by
    rw [add_assoc]
    exact tangent_chart_nonzero hw₀ hh
  have hnorm : ‖(w₀+y)+u•t‖ ≤ 2 := by
    rw [add_assoc]
    exact (norm_add_le _ _).trans (by rw [hw₀]; linarith)
  have hnear : ‖normalizedLine (w₀+y) t u - w₀‖ ≤ 2*‖y+u•t‖ := by
    have hp := norm_normalization_sub_le hw₀ hne
    simpa only [normalizedLine,add_assoc,add_sub_cancel_left] using hp
  have hfield' := hfield (normalizedLine (w₀+y) t u) v
    (normalizedLine_norm _ _ hne) (by
      have hm := mul_le_mul_of_nonneg_right hnear (norm_nonneg d)
      nlinarith)
  exact normalizedLine_phase_nonstationary _ _ _ hne hnorm hτ.le hfield'

end Falconer

end OAI
