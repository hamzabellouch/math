import OAI.Geometry.RCD.Sobolev.BochnerGramSource
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates

namespace OAI

/-! # Local replacement of the potential in a full Bochner source -/

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem IsMeasureLaplacianOn.bochner_congr {Ω : Set X} (hΩ : MeasurableSet Ω)
    (K : ℝ) {u v d G : SobolevSpace μ Q} (σ : SignedMeasure X)
    (huv : SobolevSpace.toLp μ Q u =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q v)
    (hσ : IsMeasureLaplacianOn μ Q Ω G (bochnerGramSource μ Q K u u d d σ)) :
    IsMeasureLaplacianOn μ Q Ω G (bochnerGramSource μ Q K v v d d σ) := by
  intro ψ b hb hbc hbs hψ
  let q : X →ᵇ ℝ := ofCompactSupport b hb hbc
  have hgg := (ae_restrict_iff' hΩ).mp (localGamma_pair_congr_ae μ Q huv huv)
  have hgd := (ae_restrict_iff' hΩ).mp
    (localGamma_pair_congr_ae μ Q (g := d) (g' := d) huv (EventuallyEq.refl _ _))
  have heq : signedTestIntegral q (bochnerGramSource μ Q K v v d d σ)=
      signedTestIntegral q (bochnerGramSource μ Q K u u d d σ) := by
    rw [integral_bochnerGramSource,integral_bochnerGramSource]
    congr 1
    apply integral_congr_ae
    filter_upwards [hgg,hgd] with x hx hy
    by_cases hm : x ∈ Ω
    · dsimp only [bochnerDrift]
      rw [hx hm,hy hm]
    · have hz : q x=0 := image_eq_zero_of_notMem_tsupport (fun hs => hm (hbs hs))
      simp only [hz,zero_mul]
  change energyForm μ Q G ψ= -signedTestIntegral q (bochnerGramSource μ Q K v v d d σ)
  rw [heq]
  exact hσ ψ b hb hbc hbs hψ

end RegularPointCoordinates

end

end OAI
