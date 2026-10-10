import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularState
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularAnalytic

namespace OAI

/-! Holomorphic dependence of the full regular value-and-slope state. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem spectralRegularState_analyticAt (d : ℕ) (α : ℝ) (hα : 0 < α)
    (c : ℂ × ℂ) (s : ℂ → RegularSpectralSpace) (z : ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hs : AnalyticAt ℂ s z) :
    AnalyticAt ℂ (fun lam => spectralRegularState d α c (s lam) r) z := by
  have hv := spectralRegularLift_analyticAt d α hα c s z r hr hs
  have hd := spectralRegularLift_deriv_analyticAt d α hα.le c s z r hr hs
  simp_rw [(spectralRegularLift_hasDerivAt d α c _ r).deriv] at hd
  let W : ℂ → ℂ × ℂ := fun lam => spectralRegularLift d α c (s lam) r
  let D : ℂ → ℂ × ℂ := fun lam =>
    ((r : ℂ)*spectralRegularAverage d 1 (spectralRegularWeightedSource α (s lam).1) r,
     (r : ℂ)*spectralRegularAverage d (-1) (spectralRegularWeightedSource α (s lam).2) r)
  have hvp := ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt
    (W z)).comp (f := W) (x := z) hv
  have hvm := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt
    (W z)).comp (f := W) (x := z) hv
  have hdp := ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt
    (D z)).comp (f := D) (x := z) hd
  have hdm := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt
    (D z)).comp (f := D) (x := z) hd
  exact (hvp.prod hdp).prod (hvm.prod hdm)

end DefocusingNLS

end OAI
