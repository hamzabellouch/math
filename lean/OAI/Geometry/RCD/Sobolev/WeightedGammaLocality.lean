import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates
import OAI.Analysis.RCDHeat.HeatFisher

namespace OAI

/-! # Locality under a supported measurable weight -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem weightedGamma_congr_on {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f f' g g' : SobolevSpace μ Q}
    (hf : SobolevSpace.toLp μ Q f =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q f')
    (hg : SobolevSpace.toLp μ Q g =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q g')
    (w : X → ℝ) (hw : ∀ x∉Ω, w x=0) :
    weightedGamma μ Q w f g=weightedGamma μ Q w f' g' := by
  have hlocal := (ae_restrict_iff' hΩ).mp (localGamma_pair_congr_ae μ Q hf hg)
  apply integral_congr_ae
  filter_upwards [hlocal] with x hx
  by_cases hmem : x∈Ω
  · rw [hx hmem]
  · simp only [hw x hmem,zero_mul]

end RegularPointCoordinates

end

end OAI
