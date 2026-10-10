import OAI.Analysis.KadisonKastler.GaussianStateAnalytic

namespace OAI

/-! # Bounded operators representing the derivative of Gaussian smearing -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

def gaussianDerivativeEnvelope (r R t : ℝ) : ℝ :=
  (2 * r * Real.exp (2 * r * R ^ 2)) *
    ((|t| + R) * Real.exp (-(r / 2) * t ^ 2))

theorem gaussianDerivativeEnvelope_integrable {r : ℝ} (hr : 0 < r) (R : ℝ) :
    Integrable (gaussianDerivativeEnvelope r R) :=
  gaussianStateKernelDeriv_bound_integrable hr R

theorem gaussianStateKernelDeriv_integrable {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Integrable (gaussianStateKernelDeriv r z) := by
  have hc : Continuous (gaussianStateKernelDeriv r z) := by
    unfold gaussianStateKernelDeriv gaussianStateKernel
    fun_prop
  exact (gaussianDerivativeEnvelope_integrable hr ‖z‖).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun t =>
      gaussianStateKernelDeriv_local_bound hr (norm_nonneg z) le_rfl t)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def gaussianStateAverageDeriv (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z : ℂ) : H →L[ℂ] H :=
  weightedOperatorIntegral volume (gaussianStateKernelDeriv r z)
    (gaussianStateKernelDeriv_integrable hr z) (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)

theorem gaussianStateAverage_hasDerivAt
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z : ℂ) (x : H) :
    HasDerivAt (fun w => gaussianStateAverage U hU a r hr w x)
      (gaussianStateAverageDeriv U hU a r hr z x) z := by
  apply gaussianVector_hasDerivAt
    (fun t => stateActionOrbit U a t x) (stateActionOrbit_continuous U hU a x)
    (‖a‖ * ‖x‖) ?_ r hr z
  intro t
  exact ((stateActionOrbit U a t).le_opNorm x).trans_eq (by rw [stateActionOrbit_norm])

theorem gaussianStateAverageDeriv_norm_le
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖gaussianStateAverageDeriv U hU a r hr z‖ ≤
      (∫ t : ℝ, gaussianDerivativeEnvelope r R t) * ‖a‖ := by
  have hi := gaussianStateKernelDeriv_integrable hr z
  have he := gaussianDerivativeEnvelope_integrable hr R
  have hb : (∫ t : ℝ, ‖gaussianStateKernelDeriv r z t‖) ≤
      ∫ t : ℝ, gaussianDerivativeEnvelope r R t :=
    integral_mono hi.norm he fun t => gaussianStateKernelDeriv_local_bound hr hR hz t
  exact (norm_weightedOperatorIntegral_le volume _ hi _
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (norm_nonneg a) (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg a))

end

end KadisonKastler

end OAI
