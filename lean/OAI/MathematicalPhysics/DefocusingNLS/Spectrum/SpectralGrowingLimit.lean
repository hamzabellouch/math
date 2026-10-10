import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGrowingProjection
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFlux

namespace OAI

/-! A strict growing-branch margin survives convergence of both the Cauchy
data and the complex WKB coefficients at a fixed observation point. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralGrowingCoefficient_eventual_margin
    (k delta : ℝ) (hk : 0 < k) (u : ℂ × ℂ)
    (hu : spectralScalarFlux u ≠ 0)
    (hmargin : (1/4 : ℝ)*spectralShellNorm k u ≤ ‖spectralGrowingCoefficient k delta u‖)
    (kn : ℕ → ℝ) (an bn : ℕ → ℂ) (un : ℕ → ℂ × ℂ)
    (hkn : Tendsto kn atTop (𝓝 k))
    (han : Tendsto an atTop (𝓝 (k : ℂ)))
    (hbn : Tendsto bn atTop (𝓝 ((k^2+delta : ℝ) : ℂ)))
    (hun : Tendsto un atTop (𝓝 u)) :
    ∀ᶠ n in atTop, (1/8 : ℝ)*spectralShellNorm (kn n) (un n) ≤
      ‖((un n).2+bn n*(un n).1)/(2*an n)‖ := by
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have huf := (continuous_fst.tendsto u).comp hun
  have hus := (continuous_snd.tendsto u).comp hun
  have hg := ((hus.add (hbn.mul huf)).div (han.const_mul 2)
    (mul_ne_zero (by norm_num) hkC)).norm
  have hg' : Tendsto (fun n => ‖((un n).2+bn n*(un n).1)/(2*an n)‖) atTop
      (𝓝 ‖spectralGrowingCoefficient k delta u‖) := by
    simpa only [spectralGrowingCoefficient,Function.comp_def,Pi.div_apply] using hg
  have hN : Tendsto (fun n => spectralShellNorm (kn n) (un n)) atTop
      (𝓝 (spectralShellNorm k u)) :=
    (hkn.mul huf.norm).add ((hkn.inv₀ hk.ne').mul hus.norm)
  have hNpos : 0 < spectralShellNorm k u := by
    have hval := norm_pos_iff.mpr (spectralScalarFlux_ne_zero_value u hu)
    have hterm : 0 ≤ k⁻¹*‖u.2‖ := by positivity
    change 0 < k*‖u.1‖+k⁻¹*‖u.2‖
    exact add_pos_of_pos_of_nonneg (mul_pos hk hval) hterm
  have hgap : 0 < ‖spectralGrowingCoefficient k delta u‖-(1/8 : ℝ)*spectralShellNorm k u := by
    linarith
  filter_upwards [(hg'.sub (hN.const_mul (1/8 : ℝ))).eventually (lt_mem_nhds hgap)] with n hn
  linarith

end DefocusingNLS

end OAI
