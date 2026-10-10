import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2ComplexMultiplier
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2WeightDifference
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralContinuousWeight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralUniformError
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace OAI

/-! Uniform radial coefficient convergence gives complex operator-norm
convergence of the multipliers used in the lower-order pencil. -/

open MeasureTheory Set Filter Topology
namespace DefocusingNLS

theorem spectralL2ComplexMultiplier_difference_norm (μ : Measure ℝ) (q p : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (hp : AEStronglyMeasurable p μ)
    (M N : ℝ) (hbq : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) (hbp : ∀ᵐ r ∂μ, ‖p r‖ ≤ N)
    (δ : ℝ) (hδ : ∀ᵐ r ∂μ, ‖q r-p r‖ ≤ δ) (u : Lp ℂ 2 μ) :
    ‖spectralL2ComplexMultiplier μ q hq M hbq u-
      spectralL2ComplexMultiplier μ p hp N hbp u‖ ≤ δ*‖u‖ :=
  spectralL2Weight_difference_norm μ q p hq hp M N hbq hbp δ hδ u

theorem spectralL2ComplexMultiplier_difference_opNorm (μ : Measure ℝ) (q p : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (hp : AEStronglyMeasurable p μ)
    (M N : ℝ) (hbq : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) (hbp : ∀ᵐ r ∂μ, ‖p r‖ ≤ N)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : ∀ᵐ r ∂μ, ‖q r-p r‖ ≤ δ) :
    ‖spectralL2ComplexMultiplier μ q hq M hbq-
      spectralL2ComplexMultiplier μ p hp N hbp‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hδ0
  intro u
  exact spectralL2ComplexMultiplier_difference_norm μ q p hq hp M N hbq hbp δ hδ u

noncomputable def spectralRadialWeightMultiplier (R : ℝ) (w : SpectralHarmonicWeight R) :
    SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R :=
  spectralL2ComplexMultiplier (radialPressureMeasure R) w.density
    w.radial_measurable w.bound w.radial_bound

theorem spectralRadialWeightMultiplier_tendsto (R : ℝ)
    (w : ℕ → SpectralHarmonicWeight R) (w₀ : SpectralHarmonicWeight R)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hw : ∀ n, ∀ᵐ r ∂radialPressureMeasure R,
      ‖(w n).density r-w₀.density r‖ ≤ δ n) :
    Tendsto (fun n => spectralRadialWeightMultiplier R (w n)) atTop
      (𝓝 (spectralRadialWeightMultiplier R w₀)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hδ0
  intro n
  exact spectralL2ComplexMultiplier_difference_opNorm (radialPressureMeasure R)
    (w n).density w₀.density (w n).radial_measurable w₀.radial_measurable
    (w n).bound w₀.bound (w n).radial_bound w₀.radial_bound (δ n) (hδ n) (hw n)

end DefocusingNLS

end OAI
