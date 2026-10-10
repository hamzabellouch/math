import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningCoefficient
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaleLimit
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-! Uniform convergence to the Airy coefficient on each fixed rescaled interval.
The scale limit is derived from the turning-point normalization. -/

open Filter Set Topology
namespace DefocusingNLS

theorem spectralTurningCoefficient_uniform_limit
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (M G : ℝ) (hM : 0≤M)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0<r₀ n ∧ 0≤d n ∧ 0≤eta n ∧ |gamma n|≤G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n)=0 ∧
      (r₀ n/8+2*(eta n+99/4)/(r₀ n)^3)*(d n)^3=1) :
    TendstoUniformlyOn
      (fun n xi => spectralTurningCoefficient h (b n) (eta n) (omega n) (gamma n) (r₀ n) (d n) xi)
      (fun xi => (xi : ℂ)) atTop (Icc (-M) M) := by
  have hd : Tendsto d atTop (𝓝 0) := spectralTurningScale_tendsto eta r₀ d hr₀
    (hdata.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2.2⟩))
  have hrate : Tendsto (fun n => (17/2 : ℝ)*M^2*d n+G*(d n)^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by decide : 2≠0),add_zero] using
      (hd.const_mul ((17/2 : ℝ)*M^2)).add ((hd.pow 2).const_mul G)
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  filter_upwards [hdata,hr₀.eventually (eventually_ge_atTop (max 1 (2*M))),
    hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hrate.eventually (gt_mem_nhds heps)] with n hn hr hd1 hsmall xi hxi
  have hr1 : 1≤r₀ n := (le_max_left _ _).trans hr
  have hrM : 2*M≤r₀ n := (le_max_right _ _).trans hr
  have hxiM : |xi|≤M := abs_le.mpr hxi
  have hdM : d n*M≤r₀ n/2 := by nlinarith
  have hb := spectralTurningCoefficient_bound h (b n) (eta n) (omega n) (gamma n) (r₀ n) (d n) M xi
    hn.1 hn.2.1 hn.2.2.1 hM hxiM hdM hn.2.2.2.2.1 hn.2.2.2.2.2
  have hA : 0≤(17/2 : ℝ)*M^2*d n :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M)) hn.2.1
  have hdiv : (17/2 : ℝ)*M^2*d n/r₀ n≤(17/2 : ℝ)*M^2*d n :=
    (div_le_iff₀ hn.1).mpr (by nlinarith)
  have hg := mul_le_mul_of_nonneg_right hn.2.2.2.1 (sq_nonneg (d n))
  rw [dist_comm,dist_eq_norm]
  exact (hb.trans (add_le_add hdiv hg)).trans_lt hsmall

end DefocusingNLS

end OAI
