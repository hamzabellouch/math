import OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleFar

namespace OAI

/-! The zero Fourier mode has quadratic logarithmic-frequency decay. -/
namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_triangle_trivial (N u v : ℝ) (hN : 0 < N) :
    ‖halaszTriangleIntegral N u v‖ ≤ 4*N := by
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := N/2) (b := 3*N/2) (C := (2:ℝ))
    (f := fun x => ((2/N*x-1:ℝ):ℂ)*halaszLogPhase u v x) (by
      intro x hx
      rw [norm_mul, halasz_log_phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [Set.uIoc_of_le (by linarith : N/2 ≤ 3*N/2)] at hx
      apply abs_le.mpr
      have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
      constructor <;> nlinarith [hx.1,hx.2])
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 3*N/2) (b := 5*N/2) (C := (2:ℝ))
    (f := fun x => ((-(2/N)*x+5:ℝ):ℂ)*halaszLogPhase u v x) (by
      intro x hx
      rw [norm_mul, halasz_log_phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [Set.uIoc_of_le (by linarith : 3*N/2 ≤ 5*N/2)] at hx
      apply abs_le.mpr
      have he : (-(2/N)*x)*N = -2*x := by field_simp [hN.ne']
      constructor <;> nlinarith [hx.1,hx.2])
  rw [abs_of_nonneg (by linarith : 0 ≤ 3*N/2-N/2)] at h1
  rw [abs_of_nonneg (by linarith : 0 ≤ 5*N/2-3*N/2)] at h2
  exact (norm_add_le _ _).trans (by linarith)

lemma halasz_triangle_zero_decay (N u : ℝ) (hN : 0 < N) (hu : u ≠ 0) :
    ‖halaszTriangleIntegral N u 0‖ ≤ 9300*N/u^2 := by
  have hu0 : 0 < |u| := abs_pos.mpr hu
  have hlam : 0 < 2*|u|/(5*N) := by positivity
  apply (halasz_triangle_nonstationary N u 0 (2*|u|/(5*N)) hN hlam (by
    intro x hx
    have hxp : 0 < x := (half_pos hN).trans_le hx.1
    simp only [halaszLogSlope, sub_zero, abs_div, abs_of_pos hxp]
    calc
      _ = |u|/(5*N/2) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg u) hxp hx.2)).trans_eq
  rw [← sq_abs u]
  field_simp [hN.ne', hu0.ne']
  ring

theorem halasz_triangle_zero (N u : ℝ) (hN : 0 < N) :
    ‖halaszTriangleIntegral N u 0‖ ≤ 18600*N/(1+u^2) := by
  by_cases hsmall : u^2 ≤ 1
  · apply (halasz_triangle_trivial N u 0 hN).trans
    apply (le_div_iff₀ (by positivity : 0 < 1+u^2)).mpr
    nlinarith [sq_nonneg u]
  · have hu : u ≠ 0 := by intro hu; subst u; norm_num at hsmall
    apply (halasz_triangle_zero_decay N u hN hu).trans
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero hu) (by positivity : 0 < 1+u^2)).mpr
    nlinarith

end TwoPointCorrelations

end OAI
