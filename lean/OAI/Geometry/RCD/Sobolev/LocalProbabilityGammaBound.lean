import OAI.Geometry.RCD.Heat.LocalLogarithmicSumFlux
import OAI.Geometry.RCD.Harmonic.ProbabilityDensityPairing

namespace OAI

/-! # A local gradient bound controls a pairing against a probability density -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem local_probability_gamma_bound {Ω : Set X} (hΩ : MeasurableSet Ω)
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (ρ x)))]
    (u w : SobolevSpace μ Q) {L M : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q u x ≤ L)
    (hM : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q w x ≤ M)
    (hw : ∀ᵐ x ∂μ, x ∉ Ω → SobolevSpace.toLp μ Q w x = 0) :
    |∫ x, localGamma μ Q u w x * ρ x ∂μ| ≤ L*M := by
  apply probability_density_pairing_bound μ hρ hρ0
  filter_upwards [(ae_restrict_iff' hΩ).mp hL,hM,hw,
    localGamma_abs_le μ Q u w,localGamma_zero_on_level μ Q w u 0,
    localGamma_comm μ Q u w,
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q w)]
    with x hLx hMx hwx hb hz hc hw0
  by_cases hx : x ∈ Ω
  · exact hb.trans (mul_le_mul (hLx hx) hMx hw0 hL0)
  · rw [hc,hz (hwx hx),abs_zero]
    exact mul_nonneg hL0 (hw0.trans hMx)

end RegularPointCoordinates

end

end OAI
