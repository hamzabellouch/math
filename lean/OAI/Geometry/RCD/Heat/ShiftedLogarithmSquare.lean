import OAI.Geometry.RCD.Heat.ShiftedLogarithmPairing

namespace OAI

/-! # The squared gradient of an actual shifted logarithm -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem shifted_logarithm_gamma_self (u ℓ : SobolevSpace μ hQ)
    {ε : ℝ} (hε : 0<ε) (A : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ u x∈Icc 0 (A:ℝ))
    (hℓ : SobolevSpace.toLp μ hQ ℓ =ᵐ[μ]
      fun x => Real.log (ε+SobolevSpace.toLp μ hQ u x)-Real.log ε) :
    localGamma μ hQ ℓ ℓ =ᵐ[μ] fun x => localGamma μ hQ u u x /
      (ε+SobolevSpace.toLp μ hQ u x)^2 := by
  filter_upwards [shifted_logarithm_gamma μ hQ u ℓ hε A hu hℓ ℓ,
    shifted_logarithm_gamma μ hQ u ℓ hε A hu hℓ u,
    localGamma_comm μ hQ u ℓ] with x hx hy hz
  rw [hx,hz,hy]
  rw [div_div,pow_two]

omit [ProperSpace X] in
theorem gamma_representative_bound (u H : SobolevSpace μ hQ) (L : ℝ≥0)
    (hL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x≤L)
    (hH : SobolevSpace.toLp μ hQ H =ᵐ[μ] localGamma μ hQ u u) :
    ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ H x|≤(L:ℝ)^2 := by
  filter_upwards [hH,localGamma_self μ hQ u,hL,
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ u)] with x hh hg hl hn
  rw [hh,hg,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ hn hl 2

end RegularPointCoordinates

end

end OAI
