import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRegularizedWeight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningUniformLimit

namespace OAI

/-! The continuous regularized frequency has fixed upper and lower bounds
on each scaled Airy interval, uniformly along the escaping sequence. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_central_weight_bounds
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (M G : ℝ) (hM : 0 ≤ M)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8+2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1) :
    ∀ᶠ n in atTop, 0 < d n ∧ ∀ xi ∈ Icc (-M) M,
      1 ≤ Real.sqrt (d n)*spectralTurningRegularizedWeight h (b n) (eta n) (omega n)
        (gamma n) (d n) (r₀ n+d n*xi) ∧
      Real.sqrt (d n)*spectralTurningRegularizedWeight h (b n) (eta n) (omega n)
        (gamma n) (d n) (r₀ n+d n*xi) ≤ M+3 := by
  have hu := spectralTurningCoefficient_uniform_limit h b eta omega gamma r₀ d M G hM hr₀ hdata
  filter_upwards [hdata,(Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num)] with n hn hc
  have hd : 0 < d n := by
    apply lt_of_le_of_ne hn.2.1
    intro he
    have hh := hn.2.2.2.2.2
    rw [← he] at hh
    norm_num at hh
  refine ⟨hd,?_⟩
  intro xi hxi
  apply spectralTurningRegularizedWeight_scaled_bounds h (b n) (eta n) (omega n)
    (gamma n) (r₀ n) (d n) xi M hd hM
  have he : ‖spectralTurningCoefficient h (b n) (eta n) (omega n) (gamma n) (r₀ n) (d n) xi-
      (xi : ℂ)‖ ≤ 1 := by
    simpa only [dist_eq_norm,norm_sub_rev] using (hc xi hxi).le
  have hx : ‖(xi : ℂ)‖ ≤ M := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_le.mpr hxi
  have hb := norm_add_le (spectralTurningCoefficient h (b n) (eta n) (omega n) (gamma n)
    (r₀ n) (d n) xi-(xi : ℂ)) (xi : ℂ)
  rw [sub_add_cancel] at hb
  linarith

end DefocusingNLS

end OAI
