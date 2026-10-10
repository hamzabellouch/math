import OAI.Geometry.RCD.Sobolev.MeasureLaplacianProduct
import OAI.Geometry.RCD.Sobolev.SupportedEnergyLocality

namespace OAI

/-! # Local linearity and locality of full measure Laplacians -/

open Set MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem IsMeasureLaplacianOn.add {Ω : Set X} {f g : SobolevSpace μ hQ}
    {ν τ : SignedMeasure X} (hf : IsMeasureLaplacianOn μ hQ Ω f ν)
    (hg : IsMeasureLaplacianOn μ hQ Ω g τ) :
    IsMeasureLaplacianOn μ hQ Ω (f+g) (ν+τ) := by
  intro ψ v hv hvc hvs hψ
  let q : X →ᵇ ℝ := ofCompactSupport v hv hvc
  rw [energyForm_add_left,hf ψ v hv hvc hvs hψ,hg ψ v hv hvc hvs hψ]
  have hi : (∫ᵛ x, v x ∂<•(ν+τ))=(∫ᵛ x, v x ∂<•ν)+(∫ᵛ x, v x ∂<•τ) :=
    VectorMeasure.integral_add_vectorMeasure
      (PositiveBilinearMeasure.integrable_weight q ν) (PositiveBilinearMeasure.integrable_weight q τ)
  rw [hi]
  ring

omit [ProperSpace X] [BorelSpace X] in
theorem IsMeasureLaplacianOn.smul {Ω : Set X} {f : SobolevSpace μ hQ}
    {ν : SignedMeasure X} (hf : IsMeasureLaplacianOn μ hQ Ω f ν) (c : ℝ) :
    IsMeasureLaplacianOn μ hQ Ω (c • f) (c • ν) := by
  intro ψ v hv hvc hvs hψ
  rw [energyForm_smul_left,hf ψ v hv hvc hvs hψ,VectorMeasure.integral_smul_vectorMeasure]
  simp only [smul_eq_mul]
  ring

theorem IsMeasureLaplacianOn.congr {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f g : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hf : IsMeasureLaplacianOn μ hQ Ω f ν)
    (hfg : SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ g) :
    IsMeasureLaplacianOn μ hQ Ω g ν := by
  intro ψ v hv hvc hvs hψ
  rw [← energyForm_eq_of_test_support μ hQ hΩ hfg v hψ hvs]
  exact hf ψ v hv hvc hvs hψ

end RegularPointCoordinates

end

end OAI
