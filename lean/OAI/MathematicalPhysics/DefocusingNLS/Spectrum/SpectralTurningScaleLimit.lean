import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRescale
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The Airy length tends to zero as the actual turning radius escapes.
This follows directly from its defining equation, without an assumed scale limit. -/

open Filter Set Topology
namespace DefocusingNLS

theorem spectralTurningScale_cubic (eta r₀ d : ℝ) (hr₀ : 0<r₀)
    (hd : 0≤d) (heta : 0≤eta)
    (hscale : (r₀/8+2*(eta+99/4)/r₀^3)*d^3=1) : r₀*d^3≤8 := by
  have hn : 0≤(2*(eta+99/4)/r₀^3)*d^3 := by positivity
  nlinarith

theorem spectralTurningScale_lt (eta r₀ d eps : ℝ) (hr₀ : 0<r₀)
    (hd : 0≤d) (heta : 0≤eta) (heps : 0<eps) (hlarge : 8/eps^3<r₀)
    (hscale : (r₀/8+2*(eta+99/4)/r₀^3)*d^3=1) : d<eps := by
  have hc := spectralTurningScale_cubic eta r₀ d hr₀ hd heta hscale
  have hl : 8<r₀*eps^3 := (div_lt_iff₀ (pow_pos heps 3)).mp hlarge
  by_contra hn
  have hp := pow_le_pow_left₀ heps.le (le_of_not_gt hn) 3
  have hm := mul_le_mul_of_nonneg_left hp hr₀.le
  linarith

theorem spectralTurningScale_tendsto (eta r₀ d : ℕ → ℝ)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0<r₀ n ∧ 0≤d n ∧ 0≤eta n ∧
      (r₀ n/8+2*(eta n+99/4)/(r₀ n)^3)*(d n)^3=1) :
    Tendsto d atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [hdata,hr₀.eventually (eventually_gt_atTop (8/eps^3))] with n hn hl
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hn.2.1]
  exact spectralTurningScale_lt (eta n) (r₀ n) (d n) eps hn.1 hn.2.1 hn.2.2.1 heps hl hn.2.2.2

end DefocusingNLS

end OAI
