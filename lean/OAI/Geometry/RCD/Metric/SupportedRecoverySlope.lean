import OAI.Geometry.RCD.Sobolev.RecoveryEnergyFromSlope
import OAI.Analysis.RCDHeat.RelaxedChain

namespace OAI

/-! # Extending local gradient bounds across the zero region of a recovery -/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem supported_recovery_slope (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (w : SobolevSpace μ hQ) {U : Set X} (hU : MeasurableSet U)
    {r : ℝ} {G : X → ℝ} (hG : ∀ x, 0≤G x)
    (hs : ∀ᵐ x ∂μ, x∉U → SobolevSpace.toLp μ hQ w x=0)
    (hg : ∀ᵐ x ∂μ.restrict U, r*SobolevSpace.minimalSlope μ hQ w x≤G x) :
    ∀ᵐ x ∂μ, r*SobolevSpace.minimalSlope μ hQ w x≤G x := by
  have hh := (ae_restrict_iff' hU).mp hg
  filter_upwards [hs,hh,SobolevSpace.minimalSlope_zero_on_zero μ hQ w] with x hx hy hz
  by_cases hxu : x∈U
  · exact hy hxu
  · rw [hz (hx hxu),mul_zero]
    exact hG x

omit [ProperSpace X] in
theorem recovery_energy_quadratic_error (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {Ω : Set X} [IsFiniteMeasure (μ.restrict Ω)] (hmass : 0<μ.real Ω)
    {r : ℝ} (hr : 0≤r) (w : SobolevSpace μ hQ)
    {G : X → ℝ} {D η : ℝ} (hη : 0≤η)
    (hGm : AEStronglyMeasurable G (μ.restrict Ω))
    (hG : ∀ᵐ x ∂μ.restrict Ω, 0≤G x ∧ G x≤D)
    (hgrad : ∀ᵐ x ∂μ.restrict Ω, r*SobolevSpace.minimalSlope μ hQ w x≤G x+η) :
    r^2*(μ.real Ω)⁻¹*(∫ x in Ω, localGamma μ hQ w w x ∂μ)≤
      (μ.real Ω)⁻¹*(∫ x in Ω, G x^2 ∂μ)+η*(2*D+η) := by
  have hGi : IntegrableOn (fun x => G x^2) Ω μ :=
    (integrable_const (D^2)).mono' (hGm.pow 2) (hG.mono fun x hx => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (G x))] using
        pow_le_pow_left₀ hx.1 hx.2 2)
  have hGη : IntegrableOn (fun x => (G x+η)^2) Ω μ :=
    (integrable_const ((D+η)^2)).mono' ((hGm.add_const η).pow 2) (hG.mono fun x hx => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (G x+η))] using
        pow_le_pow_left₀ (add_nonneg hx.1 hη) (add_le_add hx.2 le_rfl) 2)
  have hp : ∀ᵐ x ∂μ.restrict Ω, (G x+η)^2≤G x^2+η*(2*D+η) := by
    filter_upwards [hG] with x hx
    nlinarith [mul_nonneg hη (sub_nonneg.mpr hx.2)]
  have hi := integral_mono_ae hGη (hGi.add (integrable_const (η*(2*D+η)))) hp
  change (∫ x in Ω, (G x+η)^2 ∂μ)≤(∫ x in Ω, G x^2+η*(2*D+η) ∂μ) at hi
  rw [integral_add hGi (integrable_const _),integral_const,smul_eq_mul,
    Measure.real,Measure.restrict_apply_univ] at hi
  change (∫ x in Ω, (G x+η)^2 ∂μ)≤(∫ x in Ω, G x^2 ∂μ)+μ.real Ω*(η*(2*D+η)) at hi
  have hi' := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hmass.le)
  rw [mul_add,← mul_assoc,inv_mul_cancel₀ hmass.ne',one_mul] at hi'
  exact (rescaled_recovery_energy_le μ hQ hr w hGη hgrad).trans hi'

end RegularPointCoordinates

end

end OAI
