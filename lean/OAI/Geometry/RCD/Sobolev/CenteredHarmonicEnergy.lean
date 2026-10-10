import OAI.Geometry.RCD.Harmonic.CenteredHarmonicDirection

namespace OAI

/-! # Centering preserves the actual rescaled mixed energy -/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem rescaled_local_pairing_of_centering (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (s : Set X) {r : ℝ} (hr : r ≠ 0)
    (u v w z : SobolevSpace μ hQ)
    (hw : ∀ q : SobolevSpace μ hQ, localGamma μ hQ w q =ᵐ[μ.restrict s]
      fun x => r⁻¹*localGamma μ hQ u q x)
    (hz : ∀ q : SobolevSpace μ hQ, localGamma μ hQ z q =ᵐ[μ.restrict s]
      fun x => r⁻¹*localGamma μ hQ v q x) :
    (fun x => r^2*localGamma μ hQ w z x) =ᵐ[μ.restrict s] localGamma μ hQ u v := by
  filter_upwards [hw z,hz u,ae_restrict_of_ae (localGamma_comm μ hQ u z),
    ae_restrict_of_ae (localGamma_comm μ hQ v u)] with x h1 h2 h3 h4
  rw [h1,h3,h2,h4]
  field_simp

end RegularPointCoordinates

end

end OAI
