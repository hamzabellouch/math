import OAI.Geometry.RCD.Heat.HeatBochnerIdentitySource
import OAI.Geometry.RCD.Sobolev.BochnerCutoffFlux
import OAI.Geometry.RCD.Sobolev.HarmonicCutoffMassBound

namespace OAI

/-! # Cutoff masses of a prescribed full Bochner measure -/

open Set Filter MeasureTheory Metric
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem bochner_energy_identity_of_laplacian (K : ℝ) (u d G : SobolevSpace μ Q)
    {Ω : Set X} (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : IsMeasureLaplacianOn μ Q Ω G (bochnerGramSource μ Q K u u d d σ.toSignedMeasure))
    (ψ : SobolevSpace μ Q) (v : X → ℝ) (hv : Continuous v) (hvc : HasCompactSupport v)
    (hvs : tsupport v ⊆ Ω) (hψ : SobolevSpace.toLp μ Q ψ =ᵐ[μ] v) :
    (∫ x, v x ∂σ)=-(1/2:ℝ)*energyForm μ Q G ψ-
      K*weightedGamma μ Q v u u-weightedGamma μ Q v u d := by
  let b : X →ᵇ ℝ := ofCompactSupport v hv hvc
  have hi0 := (localGamma_memL1 μ Q u u).bdd_mul b.continuous.aestronglyMeasurable
    (Eventually.of_forall b.norm_coe_le_norm)
  have hi1 := (localGamma_memL1 μ Q u d).bdd_mul b.continuous.aestronglyMeasurable
    (Eventually.of_forall b.norm_coe_le_norm)
  have hd : (∫ x, b x*bochnerDrift μ Q K u u d d x ∂μ)=
      2*K*weightedGamma μ Q v u u+2*weightedGamma μ Q v u d := by
    have he : (fun x => b x*bochnerDrift μ Q K u u d d x)=
        fun x => 2*K*(b x*localGamma μ Q u u x)+2*(b x*localGamma μ Q u d x) := by
      funext x
      dsimp only [bochnerDrift]
      ring
    rw [he,integral_add (hi0.const_mul _) (hi1.const_mul _),integral_const_mul,integral_const_mul]
    rfl
  have he := hσ ψ v hv hvc hvs hψ
  change energyForm μ Q G ψ = -signedTestIntegral b
    (bochnerGramSource μ Q K u u d d σ.toSignedMeasure) at he
  rw [integral_bochnerGramSource,hd] at he
  change energyForm μ Q G ψ = -(2*(∫ᵛ x, b x ∂<•σ.toSignedMeasure)+_) at he
  rw [VectorMeasure.integral_toSignedMeasure] at he
  change energyForm μ Q G ψ = -(2*(∫ x, v x ∂σ)+_) at he
  linarith only [he]

variable [IsFiniteMeasureOnCompacts μ]

theorem GoodLaplacianCutoff.full_bochner_mass_identity
    {p : X} {r C K : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (u d G : SobolevSpace μ Q)
    (hd : IsWeakLaplacian μ Q u (SobolevSpace.toLp μ Q d))
    (hG : SobolevSpace.toLp μ Q G =ᵐ[μ] localGamma μ Q u u)
    {Ω : Set X} (hΩ : tsupport (χ.weight : X → ℝ) ⊆ Ω)
    (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : IsMeasureLaplacianOn μ Q Ω G (bochnerGramSource μ Q K u u d d σ.toSignedMeasure)) :
    (∫ x, χ.weight x ∂σ)=
      (1/2:ℝ)*weightedGamma μ Q χ.laplacian u u-K*weightedGamma μ Q χ.weight u u+
      (∫ x, χ.weight x*(SobolevSpace.toLp μ Q d x)^2 ∂μ)+
      weightedGamma μ Q (SobolevSpace.toLp μ Q d) u χ.sobolev := by
  have he := bochner_energy_identity_of_laplacian μ Q K u d G σ hσ
    χ.sobolev χ.weight χ.weight.continuous (χ.hasCompactSupport μ Q) hΩ χ.representative
  have hw : weightedGamma μ Q χ.weight u d=
      weightedGamma μ Q (SobolevSpace.toLp μ Q χ.sobolev) u d := by
    apply integral_congr_ae
    filter_upwards [χ.representative] with x hx
    rw [hx]
  rw [hw] at he
  have hf := χ.bochner_source_identity μ Q u d G hd hG
  linarith only [he,hf]

omit [IsFiniteMeasureOnCompacts μ] in
theorem GoodLaplacianCutoff.harmonic_full_mass_identity
    {p : X} {r C K : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (u G : SobolevSpace μ Q)
    (hG : SobolevSpace.toLp μ Q G =ᵐ[μ] localGamma μ Q u u)
    {Ω : Set X} (hΩ : tsupport (χ.weight : X → ℝ) ⊆ Ω)
    (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : IsMeasureLaplacianOn μ Q Ω G (bochnerGramSource μ Q K u u 0 0 σ.toSignedMeasure)) :
    (∫ x, χ.weight x ∂σ)=
      (1/2:ℝ)*weightedGamma μ Q χ.laplacian u u-K*weightedGamma μ Q χ.weight u u := by
  have he := bochner_energy_identity_of_laplacian μ Q K u 0 G σ hσ
    χ.sobolev χ.weight χ.weight.continuous (χ.hasCompactSupport μ Q) hΩ χ.representative
  have hE : energyForm μ Q G χ.sobolev = -weightedGamma μ Q χ.laplacian u u := by
    rw [energyForm_comm,χ.weak_laplacian,L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [hG] with x hx
    simp only [Real.inner_apply,hx]
  have hz : weightedGamma μ Q χ.weight u 0=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [localGamma_smul_right μ Q 0 u (0 : SobolevSpace μ Q)] with x hx
    change χ.weight x*localGamma μ Q u 0 x=0
    simpa only [zero_smul,zero_mul,mul_zero] using congrArg (χ.weight x * ·) hx
  rw [hE,hz] at he
  linarith only [he]

end RegularPointCoordinates

end

end OAI
