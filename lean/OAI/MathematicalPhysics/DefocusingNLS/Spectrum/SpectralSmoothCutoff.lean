import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicJetMultiplier
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! Smooth cutoffs on Schwartz functions and their exact L² product identities. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

noncomputable def spectralSmoothCutoff (q : ℝ → ℝ) : 𝓢(ℝ,ℂ) →L[ℂ] 𝓢(ℝ,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun r => (q r : ℂ))

theorem spectralSmoothCutoff_apply (q : ℝ → ℝ) (hq : q.HasTemperateGrowth)
    (f : 𝓢(ℝ,ℂ)) (r : ℝ) : spectralSmoothCutoff q f r=(q r : ℂ)*f r := by
  have hqc : (fun r => (q r : ℂ)).HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.comp hq
  rw [spectralSmoothCutoff,SchwartzMap.smulLeftCLM_apply_apply hqc]
  rfl

theorem spectralSmoothCutoff_derivative (q dq : ℝ → ℝ) (hq : q.HasTemperateGrowth)
    (hd : ∀ r, HasDerivAt q (dq r) r) (f : 𝓢(ℝ,ℂ)) (r : ℝ) :
    SchwartzMap.derivCLM ℂ ℂ (spectralSmoothCutoff q f) r=
      (dq r : ℂ)*f r+(q r : ℂ)*SchwartzMap.derivCLM ℂ ℂ f r := by
  have he : (spectralSmoothCutoff q f : ℝ → ℂ)=(fun s => (q s : ℂ)*f s) :=
    funext (spectralSmoothCutoff_apply q hq f)
  rw [SchwartzMap.derivCLM_apply,he,SchwartzMap.derivCLM_apply]
  exact ((hd r).ofReal_comp.mul (f.hasDerivAt r)).deriv

theorem spectralSmoothCutoff_L2 (μ : Measure ℝ) [IsFiniteMeasure μ]
    (q : ℝ → ℝ) (hq : q.HasTemperateGrowth) (hqm : AEStronglyMeasurable q μ)
    (M : ℝ) (hqb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) (f : 𝓢(ℝ,ℂ)) :
    spectralL2ComplexMultiplier μ q hqm M hqb
      (BoundedContinuousFunction.toLp 2 μ ℂ (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ f))=
    BoundedContinuousFunction.toLp 2 μ ℂ
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ (spectralSmoothCutoff q f)) := by
  apply Lp.ext
  filter_upwards [spectralL2ComplexMultiplier_ae μ q hqm M hqb
      (BoundedContinuousFunction.toLp 2 μ ℂ (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ f)),
    BoundedContinuousFunction.coeFn_toLp 2 μ ℂ
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ f),
    BoundedContinuousFunction.coeFn_toLp 2 μ ℂ
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ (spectralSmoothCutoff q f))]
    with r hm hf hg
  rw [hm,hf,hg]
  change q r • f r = spectralSmoothCutoff q f r
  simpa only [Complex.real_smul] using (spectralSmoothCutoff_apply q hq f r).symm

end DefocusingNLS

end OAI
