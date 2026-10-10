import OAI.Geometry.RCD.Coordinates.PositiveBilinearIntegralLower
import OAI.Geometry.RCD.Sobolev.SobolevWeakEnergyLower

namespace OAI

/-! # Integrated weighted energy lower semicontinuity for local Sobolev limits -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ) [MeasurableSpace Y]

theorem weighted_sobolev_integral_lower
    (ν : Measure Y) (u : ℕ → Y → SobolevSpace μ Q) (v : Y → SobolevSpace μ Q)
    (hu : ∀ k, AEStronglyMeasurable (u k) ν) (hv : AEStronglyMeasurable v ν)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ∀ᵐ t ∂ν, ‖u k t‖ ≤ C)
    (hvb : ∀ᵐ t ∂ν, ‖v t‖ ≤ C)
    (hc : ∀ᵐ t ∂ν, Tendsto (fun k => SobolevSpace.toLp μ Q (u k t)) atTop
      (𝓝 (SobolevSpace.toLp μ Q (v t))))
    {η : X → ℝ} (hη : AEStronglyMeasurable η μ) {M : ℝ≥0}
    (hM : ∀ᵐ x ∂μ, ‖η x‖ ≤ M) (hη0 : ∀ᵐ x ∂μ, 0 ≤ η x)
    (θ : Y → ℝ) (hθ : Integrable θ ν) (hθ0 : ∀ᵐ t ∂ν, 0 ≤ θ t)
    {A : ℝ} (he : Tendsto (fun k => ∫ t, θ t*weightedGamma μ Q η (u k t) (u k t) ∂ν)
      atTop (𝓝 A)) : (∫ t, θ t*weightedGamma μ Q η (v t) (v t) ∂ν) ≤ A := by
  let P := weightedGammaCLM μ Q hη hM
  apply positive_bilinear_integral_lower P (weightedGamma_nonneg_of_weight μ Q hη0)
    (weightedGamma_comm μ Q η) ν u v hu hv hC hb hvb _ θ hθ hθ0 he
  filter_upwards [hc,ae_all_iff.mpr hb] with t ht hb
  exact bounded_sobolev_functional_tendsto μ Q (fun k => u k t) (v t) hC hb ht (P.flip (v t))

end RegularPointCoordinates

end

end OAI
