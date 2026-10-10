import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDuhamelEstimate
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralActionError

namespace OAI

/-! Quantitative error between a true solution and the propagated initial data
of an approximate frame. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralScalarDuhamelIntegral_action_error
    (R r A C : ℝ) (hr : R≤r) (hA : 0≤A) (hC : 0≤C)
    (D U q : ℝ → ℂ × ℂ) (W : ℂ) (e : ℝ → ℂ) (k H : ℝ → ℝ)
    (hD : ContinuousOn D (Icc R r)) (hU : ContinuousOn U (Icc R r))
    (hq : ContinuousOn q (Icc R r)) (he : ContinuousOn e (Icc R r))
    (hk : ContinuousOn k (Icc R r)) (hH : ContinuousOn H (Icc R r))
    (hk0 : ∀ t ∈ Icc R r, 0<k t)
    (hkernel : ∀ t ∈ Icc R r, spectralShellNorm (k r) (spectralScalarTransferKernel D U W r t)≤
      A/k t*Real.exp (H r-H t))
    (hsolution : ∀ t ∈ Icc R r, spectralShellNorm (k t) (q t)≤
      C*Real.exp (H t+∫ s in R..t, A*‖e s‖/(k s)^2)) :
    spectralShellNorm (k r) (spectralScalarDuhamelIntegral R D U W (fun t => e t*(q t).1) r)≤
      C*Real.exp (H r+∫ s in R..r, A*‖e s‖/(k s)^2)*
        (∫ s in R..r, A*‖e s‖/(k s)^2) := by
  have hX : ContinuousOn (fun t => spectralShellNorm (k t) (q t)) (Icc R r) :=
    (hk.mul hq.fst.norm).add ((hk.inv₀ (fun t ht => (hk0 t ht).ne')).mul hq.snd.norm)
  have hg : ContinuousOn (fun t => A*‖e t‖/(k t)^2) (Icc R r) :=
    (continuousOn_const.mul he.norm).div (hk.pow 2) (fun t ht => pow_ne_zero _ (hk0 t ht).ne')
  exact (spectralScalarDuhamelIntegral_residual_bound R r A hr hA D U q W e k H
    hD hU hq he hk hH hk0 hkernel).trans
      (spectral_action_convolution_bound R r C hr hC _ _ H hX hg hH
        (fun t _ => by positivity) hsolution)

end DefocusingNLS

end OAI
