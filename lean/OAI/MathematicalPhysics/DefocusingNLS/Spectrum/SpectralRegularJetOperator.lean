import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularAverageOperator

namespace OAI

/-! Bounded linear evaluation of the regular primitive and its radial derivative. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def spectralRegularPrimitiveEvalCLM (d : ℕ) (h α r : ℝ)
    (hα : 0 < α) (hr : 0 ≤ r) : (ℝ →ᵇ ℂ) →L[ℂ] ℂ :=
  (Real.exp (α*r^2) : ℂ) • ((BoundedContinuousFunction.evalCLM ℂ r).comp
    (spectralRegularKernelCLM d h r α hr hα))

theorem spectralRegularPrimitiveEvalCLM_apply (d : ℕ) (h α r : ℝ)
    (hα : 0 < α) (hr : 0 ≤ r) (f : ℝ →ᵇ ℂ) :
    spectralRegularPrimitiveEvalCLM d h α r hα hr f=
      spectralRegularPrimitive d h (spectralRegularWeightedSource α f) r := by
  change (Real.exp (α*r^2) : ℂ)*
    ((Real.exp (-α*(radialClamp r r)^2) : ℂ)*
      spectralRegularPrimitive d h (spectralRegularWeightedSource α f) (radialClamp r r))=_
  rw [radialClamp_eq r r ⟨hr,le_rfl⟩,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  simp

noncomputable def spectralRegularSlopeEvalCLM (d : ℕ) (h α r : ℝ)
    (hα : 0 ≤ α) (hr : 0 ≤ r) : (ℝ →ᵇ ℂ) →L[ℂ] ℂ :=
  (r : ℂ) • spectralRegularAverageCLM d h α r hα hr

theorem spectralRegularSlopeEvalCLM_apply (d : ℕ) (h α r : ℝ)
    (hα : 0 ≤ α) (hr : 0 ≤ r) (f : ℝ →ᵇ ℂ) :
    spectralRegularSlopeEvalCLM d h α r hα hr f=
      (r : ℂ)*spectralRegularAverage d h (spectralRegularWeightedSource α f) r := rfl

end DefocusingNLS

end OAI
