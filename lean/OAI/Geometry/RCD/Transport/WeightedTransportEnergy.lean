import OAI.Geometry.RCD.Transport.RadialTransportError

namespace OAI

/-! # Absorbing both errors in the weak transport balance -/

open Set MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Integration and two weighted Young inequalities give a quadratic bound.
All weights and the weak balance are explicit; the radial cutoff supplies
them in the application. In particular no division by the inner norm occurs. -/
theorem weighted_transport_energy (B : Set X) (hB : MeasurableSet B)
    {w e F χ ρ ζ K : X → ℝ} {C Dχ Dρ Dζ A : ℝ}
    (hw : MemLp w 2 μ) (he : MemLp e 2 μ) (hF : MemLp F 2 μ)
    (hχ : AEStronglyMeasurable χ μ) (hρ : AEStronglyMeasurable ρ μ)
    (hζ : AEStronglyMeasurable ζ μ)
    (hwbound : ∀ᵐ x ∂μ, |w x| ≤ C)
    (hχbound : ∀ᵐ x ∂μ, 0 ≤ χ x ∧ χ x ≤ Dχ)
    (hρbound : ∀ᵐ x ∂μ, 0 ≤ ρ x ∧ ρ x ≤ Dρ)
    (hζbound : ∀ᵐ x ∂μ, 0 ≤ ζ x ∧ ζ x ≤ Dζ)
    (hK : Integrable (fun x => K x * (w x) ^ 2) μ)
    (hcoerce : ∀ᵐ x ∂μ, ζ x ≤ A * B.indicator (fun _ => (1 : ℝ)) x - K x + ρ x * e x)
    (hχcompare : ∀ᵐ x ∂μ, χ x ≤ ζ x + Dχ * B.indicator (fun _ => (1 : ℝ)) x)
    (hρcompare : ∀ᵐ x ∂μ, ρ x ≤ ζ x)
    (hbalance : (∫ x, K x * (w x) ^ 2 ∂μ) = -(∫ x, χ x * (w x * F x) ∂μ)) :
    (∫ x, ζ x * (w x) ^ 2 ∂μ) ≤
      2 * (A + Dχ / 4) * (∫ x in B, (w x) ^ 2 ∂μ) +
        2 * Dχ * (∫ x, (F x) ^ 2 ∂μ) +
        2 * C ^ 2 * Dρ * (∫ x, (e x) ^ 2 ∂μ) := by
  have hχnorm := hχbound.mono fun x hx =>
    show ‖χ x‖ ≤ Dχ by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hρnorm := hρbound.mono fun x hx =>
    show ‖ρ x‖ ≤ Dρ by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hζnorm := hζbound.mono fun x hx =>
    show ‖ζ x‖ ≤ Dζ by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hwNorm := hwbound.mono fun x hx =>
    show ‖w x‖ ≤ C by simpa only [Real.norm_eq_abs] using hx
  have hiχ := hw.integrable_sq.bdd_mul hχ hχnorm
  have hiρ := hw.integrable_sq.bdd_mul hρ hρnorm
  have hiζ := hw.integrable_sq.bdd_mul hζ hζnorm
  have hiB := hw.integrable_sq.indicator hB
  have hie : Integrable (fun x => ρ x * e x * (w x) ^ 2) μ := by
    convert ((he.integrable_mul hw).bdd_mul hw.aestronglyMeasurable hwNorm).bdd_mul hρ hρnorm using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hpoint : ∀ᵐ x ∂μ, ζ x * (w x) ^ 2 ≤
      A * B.indicator (fun x => (w x) ^ 2) x - K x * (w x) ^ 2 + ρ x * e x * (w x) ^ 2 := by
    filter_upwards [hcoerce] with x hx
    have hh := mul_le_mul_of_nonneg_right hx (sq_nonneg (w x))
    by_cases hxB : x ∈ B
    · simp only [indicator_of_mem hxB] at hh ⊢
      nlinarith only [hh]
    · simp only [indicator_of_notMem hxB] at hh ⊢
      nlinarith only [hh]
  have hmain := integral_mono_ae hiζ (((hiB.const_mul A).sub hK).add hie) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at hmain
  have hsplit := integral_add ((hiB.const_mul A).sub hK) hie
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit, integral_sub (hiB.const_mul A) hK, integral_const_mul, integral_indicator hB] at hmain
  rw [hbalance] at hmain
  have hχpoint : ∀ᵐ x ∂μ, χ x * (w x) ^ 2 ≤
      ζ x * (w x) ^ 2 + Dχ * B.indicator (fun x => (w x) ^ 2) x := by
    filter_upwards [hχcompare] with x hx
    have hh := mul_le_mul_of_nonneg_right hx (sq_nonneg (w x))
    by_cases hxB : x ∈ B
    · simp only [indicator_of_mem hxB] at hh ⊢
      nlinarith only [hh]
    · simp only [indicator_of_notMem hxB] at hh ⊢
      nlinarith only [hh]
  have hχenergy := integral_mono_ae hiχ (hiζ.add (hiB.const_mul Dχ)) hχpoint
  simp only [Pi.add_apply] at hχenergy
  rw [integral_add hiζ (hiB.const_mul Dχ), integral_const_mul, integral_indicator hB] at hχenergy
  have hρenergy := integral_mono_ae hiρ hiζ
    (hρcompare.mono fun x hx => mul_le_mul_of_nonneg_right hx (sq_nonneg (w x)))
  have hforce := radial_transport_forcing_error μ hw hF hχ hχbound
  have hcoeff := radial_transport_coefficient_error μ hw he hρ hwbound hρbound
  have hforce' := le_abs_self (∫ x, χ x * (w x * F x) ∂μ)
  have hcoeff' := le_abs_self (∫ x, ρ x * e x * (w x) ^ 2 ∂μ)
  linarith only [hmain, hforce, hcoeff, hforce', hcoeff', hχenergy, hρenergy]

end RegularPointCoordinates

end

end OAI
