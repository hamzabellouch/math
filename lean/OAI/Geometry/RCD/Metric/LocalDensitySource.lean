import OAI.Geometry.RCD.Sobolev.MeasureLaplacianAlgebra
import OAI.Geometry.RCD.Sobolev.BochnerGramSource

namespace OAI

/-! # Local replacement of the absolutely continuous source -/

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem IsMeasureLaplacianOn.sourceDensity_congr {Ω : Set X} (hΩ : MeasurableSet Ω)
    {F : SobolevSpace μ hQ} {ν : SignedMeasure X} {a b : X → ℝ}
    (hF : IsMeasureLaplacianOn μ hQ Ω F (ν+μ.withDensityᵥ a))
    (ha : Integrable a μ) (hb : Integrable b μ) (hab : a =ᵐ[μ.restrict Ω] b) :
    IsMeasureLaplacianOn μ hQ Ω F (ν+μ.withDensityᵥ b) := by
  intro ψ v hv hvc hvs hψ
  let q : X →ᵇ ℝ := ofCompactSupport v hv hvc
  have he : (fun x => q x*a x) =ᵐ[μ] fun x => q x*b x := by
    have hab' := (ae_restrict_iff' hΩ).mp hab
    filter_upwards [hab'] with x hx
    by_cases hm : x∈Ω
    · rw [hx hm]
    · have hz : q x=0 := image_eq_zero_of_notMem_tsupport (fun hs => hm (hvs hs))
      rw [hz,zero_mul,zero_mul]
  have hi : (∫ᵛ x, v x ∂<•(ν+μ.withDensityᵥ a))=(∫ᵛ x, v x ∂<•(ν+μ.withDensityᵥ b)) := by
    change (∫ᵛ x, q x ∂<•(ν+μ.withDensityᵥ a))=(∫ᵛ x, q x ∂<•(ν+μ.withDensityᵥ b))
    rw [VectorMeasure.integral_add_vectorMeasure (PositiveBilinearMeasure.integrable_weight q _)
      (PositiveBilinearMeasure.integrable_weight q _),
      VectorMeasure.integral_add_vectorMeasure (PositiveBilinearMeasure.integrable_weight q _)
      (PositiveBilinearMeasure.integrable_weight q _),integral_signedDensity μ ha,integral_signedDensity μ hb,
      integral_congr_ae he]
  rw [← hi]
  exact hF ψ v hv hvc hvs hψ

/-- A locally constant Sobolev source has zero gradient pairing there. -/
theorem localGamma_constant_source {Ω : Set X}
    (f d : SobolevSpace μ hQ) (c : ℝ)
    (hd : SobolevSpace.toLp μ hQ d =ᵐ[μ.restrict Ω] fun _ => c) :
    localGamma μ hQ f d =ᵐ[μ.restrict Ω] fun _ => 0 := by
  filter_upwards [hd,ae_restrict_of_ae (localGamma_comm μ hQ f d),
    ae_restrict_of_ae (localGamma_zero_on_level μ hQ d f c)] with x hd hc hz
  exact hc.trans (hz hd)

/-- Constant local sources remove both derivative terms in the Bochner
Gram equation, even for compact extensions of the original potential. -/
theorem IsMeasureLaplacianOn.bochner_constant_source {Ω : Set X} (hΩ : MeasurableSet Ω)
    (K : ℝ) (F f f' d : SobolevSpace μ hQ) (c : ℝ) (σ : SignedMeasure X)
    (hF : IsMeasureLaplacianOn μ hQ Ω F
      ((2:ℝ) • σ+μ.withDensityᵥ (fun x => 2*K*localGamma μ hQ f f x)))
    (hff : SobolevSpace.toLp μ hQ f' =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ f)
    (hd : SobolevSpace.toLp μ hQ d =ᵐ[μ.restrict Ω] fun _ => c) :
    IsMeasureLaplacianOn μ hQ Ω F (bochnerGramSource μ hQ K f' f' d d σ) := by
  apply hF.sourceDensity_congr μ hQ hΩ
    ((localGamma_memL1 μ hQ f f).const_mul (2*K)) (bochnerDrift_integrable μ hQ K f' f' d d)
  filter_upwards [localGamma_pair_congr_ae μ hQ hff hff,
    localGamma_constant_source μ hQ f' d c hd] with x he hz
  dsimp only [bochnerDrift]
  rw [he,hz]
  ring

theorem IsMeasureLaplacianOn.bochner_constant_source_shifted {Ω : Set X}
    (hΩ : MeasurableSet Ω) (κ : ℝ) (F f f' d : SobolevSpace μ hQ) (c : ℝ)
    (σ : SignedMeasure X)
    (hF : IsMeasureLaplacianOn μ hQ Ω F
      ((2:ℝ) • σ-(2*κ) • μ.withDensityᵥ (localGamma μ hQ f f)))
    (hff : SobolevSpace.toLp μ hQ f' =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ f)
    (hd : SobolevSpace.toLp μ hQ d =ᵐ[μ.restrict Ω] fun _ => c) :
    IsMeasureLaplacianOn μ hQ Ω F (bochnerGramSource μ hQ (-κ) f' f' d d σ) := by
  have he : μ.withDensityᵥ (fun x => 2*(-κ)*localGamma μ hQ f f x)=
      -(2*κ) • μ.withDensityᵥ (localGamma μ hQ f f) := by
    change μ.withDensityᵥ ((2*(-κ)) • localGamma μ hQ f f)=_
    rw [withDensityᵥ_smul,show 2*(-κ)=-(2*κ) by ring]
  apply IsMeasureLaplacianOn.bochner_constant_source μ hQ hΩ (-κ) F f f' d c σ _ hff hd
  rw [he,neg_smul,← sub_eq_add_neg]
  exact hF

end RegularPointCoordinates

end

end OAI
