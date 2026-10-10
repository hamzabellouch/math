import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularParameterDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularState

namespace OAI

/-! Evaluation of a parameter derivative commutes with both components of the
regular physical jet. The differentiated initial data vanish. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem spectralRegularState_hasParameterDerivAt (d : ℕ) (α : ℝ) (hα : 0 < α)
    (c : ℂ × ℂ) (s : ℂ → RegularSpectralSpace) (ds : RegularSpectralSpace)
    (z : ℂ) (hs : HasDerivAt s ds z) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivAt (fun lam => spectralRegularState d α c (s lam) r)
      (spectralRegularState d α 0 ds r) z := by
  have hp := (ContinuousLinearMap.fst ℂ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ)).hasFDerivAt.comp_hasDerivAt z hs
  have hm := (ContinuousLinearMap.snd ℂ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ)).hasFDerivAt.comp_hasDerivAt z hs
  have hp0 := (spectralRegularPrimitiveEvalCLM d 1 α r hα hr).hasFDerivAt.comp_hasDerivAt z hp
  have hm0 := (spectralRegularPrimitiveEvalCLM d (-1) α r hα hr).hasFDerivAt.comp_hasDerivAt z hm
  have hp1 := (spectralRegularSlopeEvalCLM d 1 α r hα.le hr).hasFDerivAt.comp_hasDerivAt z hp
  have hm1 := (spectralRegularSlopeEvalCLM d (-1) α r hα.le hr).hasFDerivAt.comp_hasDerivAt z hm
  simpa only [Function.comp_apply, spectralRegularState, spectralRegularLift, spectralRegularPrimitiveEvalCLM_apply,
    spectralRegularSlopeEvalCLM_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Prod.fst_zero, Prod.snd_zero, zero_add] using
    ((hp0.const_add c.1).prodMk hp1).prodMk ((hm0.const_add c.2).prodMk hm1)

theorem spectralRegularSolutionState_parameter_deriv (d : ℕ) (R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ)
    (c : ℂ × ℂ) (z : ℂ)
    (hgap : spectralRegularSourceBound A B (cp + Complex.I * z) (cm - Complex.I * z) < 2 * α)
    (r : ℝ) (hr : 0 ≤ r) :
    deriv (fun lam => spectralRegularState d α c
      (spectralRegularSolutionSource d R α hR hα A B cp cm c lam) r) z =
      spectralRegularState d α 0
        (deriv (spectralRegularSolutionSource d R α hR hα A B cp cm c) z) r :=
  (spectralRegularState_hasParameterDerivAt d α hα c _ _ z
    (spectralRegularSolutionSource_analyticAt d R α hR hα A B cp cm c z hgap).differentiableAt.hasDerivAt r hr).deriv

end DefocusingNLS

end OAI
