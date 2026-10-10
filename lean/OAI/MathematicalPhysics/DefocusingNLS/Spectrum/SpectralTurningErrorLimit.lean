import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaleLimit
import Mathlib.Analysis.Real.Sqrt

namespace OAI

/-! The outer residual vanishes in the order of choices used at the turn:
first the fixed cutoff grows, then the physical turning radius escapes. -/

open Filter Topology
namespace DefocusingNLS

noncomputable def spectralTurningCutoffError (M : ℝ) : ℝ :=
  5/(3*(Real.sqrt (M/8))^3)

noncomputable def spectralTurningOuterError (M r₀ d : ℝ) : ℝ :=
  spectralTurningCutoffError M + 3*d/(r₀*Real.sqrt (M/8)) + 8/r₀^2

theorem spectralTurningCutoffError_tendsto :
    Tendsto spectralTurningCutoffError atTop (𝓝 0) := by
  have hdiv : Tendsto (fun M : ℝ => M/8) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) tendsto_id
  have hs := Real.tendsto_sqrt_atTop.comp hdiv
  have hc := (tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).comp hs
  have hi := tendsto_inv_atTop_zero.comp hc
  have hh := hi.const_mul (5/3 : ℝ)
  change Tendsto (fun M : ℝ => 5/(3*(Real.sqrt (M/8))^3)) atTop (𝓝 0)
  convert hh using 1
  · funext M
    dsimp only [Function.comp_def]
    ring
  · simp only [mul_zero]

theorem spectralTurningOuterError_tendsto (M : ℝ) (r₀ d : ℕ → ℝ)
    (hr₀ : Tendsto r₀ atTop atTop) (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => spectralTurningOuterError M (r₀ n) (d n)) atTop
      (𝓝 (spectralTurningCutoffError M)) := by
  have hi := tendsto_inv_atTop_zero.comp hr₀
  have hnear := (hd.mul hi).const_mul (3/Real.sqrt (M/8))
  have hfar := (hi.pow 2).const_mul (8 : ℝ)
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => spectralTurningCutoffError M)
    atTop (𝓝 (spectralTurningCutoffError M))).add (hnear.add hfar)
  convert hlim using 1
  · funext n
    dsimp only [spectralTurningOuterError,Function.comp_def]
    ring
  · simp only [mul_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),add_zero]

end DefocusingNLS

end OAI
