import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningErrorLimit

namespace OAI

/-! Limit of the explicit forbidden-side residual bound, with the inner
radius fixed and the Airy cutoff chosen before the escaping sequence. -/

open Filter Topology
namespace DefocusingNLS

noncomputable def spectralTurningNegativeError (M R r₀ d : ℝ) : ℝ :=
  spectralTurningCutoffError M+3*d/(r₀*Real.sqrt (M/8))+64/(r₀*R)

theorem spectralTurningNegativeError_tendsto (M R : ℝ) (r₀ d : ℕ → ℝ)
    (hr₀ : Tendsto r₀ atTop atTop) (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => spectralTurningNegativeError M R (r₀ n) (d n)) atTop
      (𝓝 (spectralTurningCutoffError M)) := by
  have hi := tendsto_inv_atTop_zero.comp hr₀
  have hnear := (hd.mul hi).const_mul (3/Real.sqrt (M/8))
  have hfar := hi.const_mul (64/R)
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => spectralTurningCutoffError M)
    atTop (𝓝 (spectralTurningCutoffError M))).add (hnear.add hfar)
  convert hlim using 1
  · funext n
    dsimp only [spectralTurningNegativeError,Function.comp_def]
    ring
  · simp only [mul_zero,add_zero]

end DefocusingNLS

end OAI
