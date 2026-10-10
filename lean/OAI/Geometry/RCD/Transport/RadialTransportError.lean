import OAI.Geometry.RCD.Coordinates.NormalizedLocalL2

namespace OAI

/-! # The quadratic coefficient error in radial transport

The bounded unnormalized residual is used before division by its inner-ball
norm. Weighted Young's inequality preserves the square of the Poisson error.
-/

open MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The transport coefficient error absorbs one quarter of the weighted
residual energy and costs the SQUARE of the original Poisson error. -/
theorem radial_transport_coefficient_error {w e ρ : X → ℝ} {C D : ℝ}
    (hw : MemLp w 2 μ) (he : MemLp e 2 μ) (hρ : AEStronglyMeasurable ρ μ)
    (hwbound : ∀ᵐ x ∂μ, |w x| ≤ C)
    (hρbound : ∀ᵐ x ∂μ, 0 ≤ ρ x ∧ ρ x ≤ D) :
    |∫ x, ρ x * e x * (w x) ^ 2 ∂μ| ≤
      (1 / 4 : ℝ) * (∫ x, ρ x * (w x) ^ 2 ∂μ) +
        C ^ 2 * D * (∫ x, (e x) ^ 2 ∂μ) := by
  have hiw : Integrable (fun x => ρ x * (w x) ^ 2) μ :=
    hw.integrable_sq.bdd_mul hρ (hρbound.mono fun x hx => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
  have hiR : Integrable (fun x => (1 / 4 : ℝ) * (ρ x * (w x) ^ 2) +
      C ^ 2 * D * (e x) ^ 2) μ := (hiw.const_mul _).add (he.integrable_sq.const_mul _)
  have hb : ∀ᵐ x ∂μ, |ρ x * e x * (w x) ^ 2| ≤
      (1 / 4 : ℝ) * (ρ x * (w x) ^ 2) + C ^ 2 * D * (e x) ^ 2 := by
    filter_upwards [hwbound, hρbound] with x hx hρx
    have hy : |e x| * (w x) ^ 2 ≤ (w x) ^ 2 / 4 + C ^ 2 * (e x) ^ 2 := by
      have hh : |e x| * (w x) ^ 2 ≤ C * |e x| * |w x| := by
        calc
          _ = |w x| * (|e x| * |w x|) := by rw [← sq_abs (w x)]; ring
          _ ≤ C * (|e x| * |w x|) :=
            mul_le_mul_of_nonneg_right hx (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = _ := by ring
      have hs := sq_nonneg (|w x| / 2 - C * |e x|)
      rw [sub_sq, div_pow, mul_pow, sq_abs, sq_abs] at hs
      nlinarith only [hh, hs]
    calc
      _ = ρ x * (|e x| * (w x) ^ 2) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hρx.1, abs_pow, sq_abs]
        ring
      _ ≤ ρ x * ((w x) ^ 2 / 4 + C ^ 2 * (e x) ^ 2) := mul_le_mul_of_nonneg_left hy hρx.1
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hρx.2 (mul_nonneg (sq_nonneg C) (sq_nonneg (e x)))
        nlinarith only [hh]
  have hi : Integrable (fun x => ρ x * e x * (w x) ^ 2) μ :=
    hiR.mono' ((hρ.mul he.aestronglyMeasurable).mul (hw.aestronglyMeasurable.pow 2))
      (hb.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  calc
    _ ≤ ∫ x, |ρ x * e x * (w x) ^ 2| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (1 / 4 : ℝ) * (ρ x * (w x) ^ 2) + C ^ 2 * D * (e x) ^ 2 ∂μ :=
      integral_mono_ae hi.abs hiR hb
    _ = _ := by
      rw [integral_add (hiw.const_mul _) (he.integrable_sq.const_mul _),
        integral_const_mul, integral_const_mul]

/-- The inhomogeneous forcing term absorbs another quarter of the
weighted residual energy. Only its original L2 norm enters the remainder. -/
theorem radial_transport_forcing_error {w F ρ : X → ℝ} {D : ℝ}
    (hw : MemLp w 2 μ) (hF : MemLp F 2 μ) (hρ : AEStronglyMeasurable ρ μ)
    (hρbound : ∀ᵐ x ∂μ, 0 ≤ ρ x ∧ ρ x ≤ D) :
    |∫ x, ρ x * (w x * F x) ∂μ| ≤
      (1 / 4 : ℝ) * (∫ x, ρ x * (w x) ^ 2 ∂μ) +
        D * (∫ x, (F x) ^ 2 ∂μ) := by
  have hρnorm : ∀ᵐ x ∂μ, ‖ρ x‖ ≤ D := hρbound.mono fun x hx => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hiw : Integrable (fun x => ρ x * (w x) ^ 2) μ := hw.integrable_sq.bdd_mul hρ hρnorm
  have hi : Integrable (fun x => ρ x * (w x * F x)) μ :=
    (hw.integrable_mul hF).bdd_mul hρ hρnorm
  have hiR : Integrable (fun x => (1 / 4 : ℝ) * (ρ x * (w x) ^ 2) + D * (F x) ^ 2) μ :=
    (hiw.const_mul _).add (hF.integrable_sq.const_mul _)
  have hb : ∀ᵐ x ∂μ, |ρ x * (w x * F x)| ≤
      (1 / 4 : ℝ) * (ρ x * (w x) ^ 2) + D * (F x) ^ 2 := by
    filter_upwards [hρbound] with x hx
    have hs := sq_nonneg (|w x| / 2 - |F x|)
    rw [sub_sq, div_pow, sq_abs, sq_abs] at hs
    have hy : |w x| * |F x| ≤ (w x) ^ 2 / 4 + (F x) ^ 2 := by nlinarith only [hs]
    rw [abs_mul, abs_of_nonneg hx.1, abs_mul]
    have h₁ := mul_le_mul_of_nonneg_left hy hx.1
    have h₂ := mul_le_mul_of_nonneg_right hx.2 (sq_nonneg (F x))
    nlinarith only [h₁, h₂]
  calc
    _ ≤ ∫ x, |ρ x * (w x * F x)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (1 / 4 : ℝ) * (ρ x * (w x) ^ 2) + D * (F x) ^ 2 ∂μ :=
      integral_mono_ae hi.abs hiR hb
    _ = _ := by
      rw [integral_add (hiw.const_mul _) (hF.integrable_sq.const_mul _),
        integral_const_mul, integral_const_mul]

end RegularPointCoordinates

end

end OAI
