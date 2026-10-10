import OAI.Geometry.RCD.Sobolev.BochnerMeasureFromSource

namespace OAI

/-! # The full Bochner measure identity supplies the prescribed local source -/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem bochner_laplacian_of_energy_identity (K : ℝ) (u d G : SobolevSpace μ Q)
    (hG : SobolevSpace.toLp μ Q G =ᵐ[μ] localGamma μ Q u u)
    {Ω : Set X} (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : ∀ (ψ : SobolevSpace μ Q) (v : X → ℝ), Continuous v → HasCompactSupport v →
      tsupport v ⊆ Ω → SobolevSpace.toLp μ Q ψ =ᵐ[μ] v →
      (∫ x, v x ∂σ)=-(1/2:ℝ)*energyForm μ Q G ψ-
        weightedGamma μ Q (SobolevSpace.toLp μ Q ψ) u d-K*weightedGamma μ Q v u u) :
    IsMeasureLaplacianOn μ Q Ω G (bochnerGramSource μ Q K u u d d σ.toSignedMeasure) := by
  apply bochner_measure_laplacian_of_source μ Q K u d G hG σ
  intro ψ v hv hvc hvs hψ
  have he : inner ℝ (SobolevSpace.toLp μ Q ψ) (SobolevSpace.toLp μ Q G)=
      weightedGamma μ Q v u u := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hψ,hG] with x hx hg
    change SobolevSpace.toLp μ Q G x*SobolevSpace.toLp μ Q ψ x=
      v x*localGamma μ Q u u x
    rw [hx,hg]
    ring
  rw [he]
  linarith only [hσ ψ v hv hvc hvs hψ]

end RegularPointCoordinates

end

end OAI
