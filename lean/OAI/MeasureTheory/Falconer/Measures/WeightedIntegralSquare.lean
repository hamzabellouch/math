import OAI.MeasureTheory.Falconer.Fourier.SpatialFourierSeparation

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem weighted_integral_square {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w f : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hiw : Integrable w μ)
    (hif : Integrable (fun x => w x * f x) μ)
    (hif₂ : Integrable (fun x => w x * (f x)^2) μ) :
    (∫ x, w x * f x ∂μ)^2 ≤ (∫ x, w x ∂μ) * (∫ x, w x * (f x)^2 ∂μ) := by
  let W := ∫ x, w x ∂μ
  let V := ∫ x, w x * f x ∂μ
  let U := ∫ x, w x * (f x)^2 ∂μ
  have hW : 0 ≤ W := integral_nonneg hw
  by_cases hz : W = 0
  · have hwz : w =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hw hiw).mp hz
    have hvz : V = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hwz] with x hx
      simp [hx]
    change V^2 ≤ W*U
    simp [hvz,hz]
  · have hWp : 0 < W := lt_of_le_of_ne hW (Ne.symm hz)
    have hn : 0 ≤ ∫ x, w x * (f x - V/W)^2 ∂μ :=
      integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg _))
    have he (x : α) : w x * (f x - V/W)^2 =
        w x*(f x)^2 - (2*(V/W))*(w x*f x) + (V/W)^2*w x := by ring
    simp_rw [he] at hn
    have hiSub : Integrable (fun x => w x*(f x)^2 - (2*(V/W))*(w x*f x)) μ :=
      hif₂.sub (hif.const_mul (2*(V/W)))
    rw [integral_add hiSub (hiw.const_mul ((V/W)^2)),
      integral_sub hif₂ (hif.const_mul (2*(V/W))), integral_const_mul, integral_const_mul] at hn
    change 0 ≤ U - (2*(V/W))*V + (V/W)^2*W at hn
    have hc : U - (2*(V/W))*V + (V/W)^2*W = U - V^2/W := by
      field_simp
      ring
    rw [hc] at hn
    change V^2 ≤ W*U
    have hh := (div_le_iff₀ hWp).mp (show V^2/W ≤ U by linarith)
    nlinarith

theorem norm_integral_coeff_square {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c F : α → ℂ) (hic : Integrable c μ)
    (hi₁ : Integrable (fun x => ‖c x‖ * ‖F x‖) μ)
    (hi₂ : Integrable (fun x => ‖c x‖ * ‖F x‖^2) μ) :
    ‖∫ x, c x * F x ∂μ‖^2 ≤
      (∫ x, ‖c x‖ ∂μ) * (∫ x, ‖c x‖ * ‖F x‖^2 ∂μ) := by
  have hn : ‖∫ x, c x * F x ∂μ‖ ≤ ∫ x, ‖c x‖ * ‖F x‖ ∂μ := by
    simpa only [norm_mul] using norm_integral_le_integral_norm (fun x => c x * F x)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (weighted_integral_square μ (fun x => ‖c x‖) (fun x => ‖F x‖)
      (fun x => norm_nonneg _) hic.norm hi₁ hi₂)

end PlanarFalconer

end OAI
