import OAI.Geometry.RCD.Metric.SupportedRecoverySlope

namespace OAI

/-! # Weighted energy error from the sharp pointwise recovery slope -/

open Set MeasureTheory Filter
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem weighted_recovery_energy_error (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {Ω : Set X} [IsFiniteMeasure (μ.restrict Ω)] (hmass : 0<μ.real Ω)
    {r : ℝ} (hr : 0≤r) (w : SobolevSpace μ hQ)
    {G φ : X → ℝ} {D B η : ℝ} (hD : 0≤D) (hη : 0≤η)
    (hGm : AEStronglyMeasurable G (μ.restrict Ω))
    (hφm : AEStronglyMeasurable φ (μ.restrict Ω))
    (hG : ∀ᵐ x ∂μ.restrict Ω, 0≤G x ∧ G x≤D)
    (hφ : ∀ᵐ x ∂μ.restrict Ω, 0≤φ x ∧ φ x≤B)
    (hgrad : ∀ᵐ x ∂μ.restrict Ω, r*SobolevSpace.minimalSlope μ hQ w x≤G x+η) :
    r^2*(μ.real Ω)⁻¹*(∫ x in Ω, φ x*localGamma μ hQ w w x ∂μ)≤
      (μ.real Ω)⁻¹*(∫ x in Ω, φ x*G x^2 ∂μ)+B*η*(2*D+η) := by
  have hφnorm : ∀ᵐ x ∂μ.restrict Ω, ‖φ x‖≤B := hφ.mono fun x hx => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hGi : IntegrableOn (fun x => G x^2) Ω μ :=
    (integrable_const (D^2)).mono' (hGm.pow 2) (hG.mono fun x hx => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (G x))] using
        pow_le_pow_left₀ hx.1 hx.2 2)
  have hleft := ((localGamma_memL1 μ hQ w w).restrict.bdd_mul hφm hφnorm).const_mul (r^2)
  have hright := hGi.bdd_mul hφm hφnorm
  have hi : (∫ x in Ω, r^2*(φ x*localGamma μ hQ w w x) ∂μ)≤
      ∫ x in Ω, φ x*G x^2+B*η*(2*D+η) ∂μ := by
    apply integral_mono_ae hleft (hright.add (integrable_const _))
    filter_upwards [hG,hφ,hgrad,ae_restrict_of_ae (localGamma_self μ hQ w),
      ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ w))]
      with x hg hφx hs he hn
    have hsq := pow_le_pow_left₀ (mul_nonneg hr hn) hs 2
    rw [mul_pow,← he] at hsq
    have henergy : r^2*localGamma μ hQ w w x≤G x^2+η*(2*D+η) := by
      nlinarith [mul_nonneg hη (sub_nonneg.mpr hg.2)]
    have hmul := mul_le_mul_of_nonneg_left henergy hφx.1
    have herr := mul_le_mul_of_nonneg_right hφx.2
      (mul_nonneg hη (add_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hD) hη))
    change r^2*(φ x*localGamma μ hQ w w x)≤φ x*G x^2+B*η*(2*D+η)
    nlinarith only [hmul,herr]
  rw [integral_const_mul,integral_add hright (integrable_const _),
    integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ] at hi
  change r^2*(∫ x in Ω, φ x*localGamma μ hQ w w x ∂μ)≤
    (∫ x in Ω, φ x*G x^2 ∂μ)+μ.real Ω*(B*η*(2*D+η)) at hi
  have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hmass.le)
  rw [mul_add,← mul_assoc (μ.real Ω)⁻¹ (μ.real Ω),inv_mul_cancel₀ hmass.ne',one_mul] at hh
  simpa only [mul_left_comm (μ.real Ω)⁻¹,mul_assoc] using hh

end RegularPointCoordinates

end

end OAI
