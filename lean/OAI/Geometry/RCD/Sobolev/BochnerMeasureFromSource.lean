import OAI.Geometry.RCD.Sobolev.BochnerGramSource

namespace OAI

/-! # The full measure Laplacian from the continuous Bochner test identity -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem bochner_measure_laplacian_of_source (K : ℝ) (u d G : SobolevSpace μ Q)
    (hG : SobolevSpace.toLp μ Q G =ᵐ[μ] localGamma μ Q u u)
    {Ω : Set X} (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : ∀ (ψ : SobolevSpace μ Q) (v : X → ℝ), Continuous v → HasCompactSupport v →
      tsupport v ⊆ Ω → SobolevSpace.toLp μ Q ψ =ᵐ[μ] v →
      (∫ x, v x ∂σ)=-(1/2:ℝ)*energyForm μ Q G ψ-
        K*inner ℝ (SobolevSpace.toLp μ Q ψ) (SobolevSpace.toLp μ Q G)-
        weightedGamma μ Q (SobolevSpace.toLp μ Q ψ) u d) :
    IsMeasureLaplacianOn μ Q Ω G (bochnerGramSource μ Q K u u d d σ.toSignedMeasure) := by
  intro ψ v hv hvc hvs hψ
  let q : X →ᵇ ℝ := ofCompactSupport v hv hvc
  have hi0 := (localGamma_memL1 μ Q u u).bdd_mul q.continuous.aestronglyMeasurable
    (Eventually.of_forall q.norm_coe_le_norm)
  have hi1 := (localGamma_memL1 μ Q u d).bdd_mul q.continuous.aestronglyMeasurable
    (Eventually.of_forall q.norm_coe_le_norm)
  have hI : inner ℝ (SobolevSpace.toLp μ Q ψ) (SobolevSpace.toLp μ Q G)=
      ∫ x, q x*localGamma μ Q u u x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hψ,hG] with x hx hg
    simp only [Real.inner_apply,hx,hg]
    rfl
  have hJ : weightedGamma μ Q (SobolevSpace.toLp μ Q ψ) u d=
      ∫ x, q x*localGamma μ Q u d x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hψ] with x hx
    rw [hx]
    rfl
  have hd : (∫ x, q x*bochnerDrift μ Q K u u d d x ∂μ)=
      2*K*inner ℝ (SobolevSpace.toLp μ Q ψ) (SobolevSpace.toLp μ Q G)+
        2*weightedGamma μ Q (SobolevSpace.toLp μ Q ψ) u d := by
    rw [hI,hJ]
    have he : (fun x => q x*bochnerDrift μ Q K u u d d x)=
        fun x => 2*K*(q x*localGamma μ Q u u x)+2*(q x*localGamma μ Q u d x) := by
      funext x
      dsimp only [bochnerDrift]
      ring
    rw [he,integral_add (hi0.const_mul _) (hi1.const_mul _),integral_const_mul,integral_const_mul]
  have hs : signedTestIntegral q (bochnerGramSource μ Q K u u d d σ.toSignedMeasure)=
      2*(∫ x, v x ∂σ)+2*K*inner ℝ (SobolevSpace.toLp μ Q ψ) (SobolevSpace.toLp μ Q G)+
        2*weightedGamma μ Q (SobolevSpace.toLp μ Q ψ) u d := by
    rw [integral_bochnerGramSource,hd]
    change 2*(∫ᵛ x, q x ∂<•σ.toSignedMeasure)+_= _
    rw [VectorMeasure.integral_toSignedMeasure]
    change 2*(∫ x, v x ∂σ)+_= _
    ring
  have hh := hσ ψ v hv hvc hvs hψ
  change energyForm μ Q G ψ= -signedTestIntegral q (bochnerGramSource μ Q K u u d d σ.toSignedMeasure)
  rw [hs,hh]
  ring

end RegularPointCoordinates

end

end OAI
