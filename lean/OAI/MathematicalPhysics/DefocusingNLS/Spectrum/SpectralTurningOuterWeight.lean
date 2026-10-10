import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRegularizedWeight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningUniformLimit

namespace OAI

/-! Monotonicity of the actual frequency identifies the regularized norm
with the WKB norm on each outer interval. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurningRegularizedWeight_left (h b eta omega gamma d a r : ℝ)
    (hd : 0 < d) (heta : 0 ≤ eta) (hr : 0 < r) (ha : 0 < a) (hra : r ≤ a)
    (hFa : homogeneousSpectralLocalizationFrequency h b eta omega a ≤ 0)
    (hlarge : 1 ≤ d^2*|homogeneousSpectralLocalizationFrequency h b eta omega a|) :
    spectralTurningRegularizedWeight h b eta omega gamma d r =
      Real.sqrt ‖spectralLiouvilleMomentum (-1) h b eta omega gamma r‖ := by
  have hm := (homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta).monotoneOn hr ha hra
  have hFr := hm.trans hFa
  have habs : |homogeneousSpectralLocalizationFrequency h b eta omega a| ≤
      |homogeneousSpectralLocalizationFrequency h b eta omega r| := by
    rw [abs_of_nonpos hFa,abs_of_nonpos hFr]
    linarith
  have he := spectralTurningRegularizedWeight_eq_of_frequency h b eta omega gamma d r hd
    (hlarge.trans (mul_le_mul_of_nonneg_left habs (sq_nonneg d)))
  exact he.trans (spectralLiouville_weight_sign (-1) h b eta omega gamma r (by norm_num)).symm

theorem spectralTurningRegularizedWeight_right (h b eta omega gamma d a r : ℝ)
    (hd : 0 < d) (heta : 0 ≤ eta) (hr : 0 < r) (ha : 0 < a) (har : a ≤ r)
    (hFa : 0 ≤ homogeneousSpectralLocalizationFrequency h b eta omega a)
    (hlarge : 1 ≤ d^2*|homogeneousSpectralLocalizationFrequency h b eta omega a|) :
    spectralTurningRegularizedWeight h b eta omega gamma d r =
      Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma r‖ := by
  have hm := (homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta).monotoneOn ha hr har
  have hFr := hFa.trans hm
  have habs : |homogeneousSpectralLocalizationFrequency h b eta omega a| ≤
      |homogeneousSpectralLocalizationFrequency h b eta omega r| := by
    rwa [abs_of_nonneg hFa,abs_of_nonneg hFr]
  exact spectralTurningRegularizedWeight_eq_of_frequency h b eta omega gamma d r hd
    (hlarge.trans (mul_le_mul_of_nonneg_left habs (sq_nonneg d)))

theorem spectralTurningCoefficient_real_error (h b eta omega gamma r₀ d xi : ℝ)
    (herr : ‖spectralTurningCoefficient h b eta omega gamma r₀ d xi-(xi : ℂ)‖ ≤ 1) :
    |d^2*homogeneousSpectralLocalizationFrequency h b eta omega (r₀+d*xi)-xi| ≤ 1 := by
  have hh := (Complex.abs_re_le_norm (spectralTurningCoefficient h b eta omega gamma r₀ d xi-(xi : ℂ))).trans herr
  simpa only [spectralTurningCoefficient,Complex.sub_re,Complex.mul_re,Complex.add_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    sub_zero,add_zero] using hh


theorem spectralTurning_regularized_outer_weights
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (M G : ℝ) (hM : 2 ≤ M)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8+2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1) :
    ∀ᶠ n in atTop,
      (∀ r : ℝ, 0 < r → r ≤ r₀ n-d n*M →
        spectralTurningRegularizedWeight h (b n) (eta n) (omega n) (gamma n) (d n) r =
          Real.sqrt ‖spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) r‖) ∧
      (∀ r : ℝ, r₀ n+d n*M ≤ r →
        spectralTurningRegularizedWeight h (b n) (eta n) (omega n) (gamma n) (d n) r =
          Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n) (eta n) (omega n) (gamma n) r‖) := by
  have hM0 : 0 ≤ M := by linarith
  have hu := spectralTurningCoefficient_uniform_limit h b eta omega gamma r₀ d M G hM0 hr₀ hdata
  filter_upwards [hdata,(Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num)] with n hn hc
  have hd : 0 < d n := by
    apply lt_of_le_of_ne hn.2.1
    intro he
    have hh := hn.2.2.2.2.2
    rw [← he] at hh
    norm_num at hh
  have hleft := spectralTurningCoefficient_real_error h (b n) (eta n) (omega n) (gamma n)
    (r₀ n) (d n) (-M) (by
      simpa only [dist_eq_norm,norm_sub_rev] using (hc (-M) ⟨le_rfl,by linarith⟩).le)
  have hright := spectralTurningCoefficient_real_error h (b n) (eta n) (omega n) (gamma n)
    (r₀ n) (d n) M (by
      simpa only [dist_eq_norm,norm_sub_rev] using (hc M ⟨by linarith,le_rfl⟩).le)
  have heq : r₀ n+d n*(-M) = r₀ n-d n*M := by ring
  rw [heq] at hleft
  have hFl : homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n-d n*M) ≤ 0 := by
    nlinarith [abs_le.mp hleft,sq_nonneg (d n)]
  have hFr : 0 ≤ homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n+d n*M) := by
    nlinarith [abs_le.mp hright,sq_nonneg (d n)]
  have hLargeL : 1 ≤ (d n)^2*|homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n-d n*M)| := by
    rw [abs_of_nonpos hFl]
    nlinarith [abs_le.mp hleft]
  have hLargeR : 1 ≤ (d n)^2*|homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n+d n*M)| := by
    rw [abs_of_nonneg hFr]
    nlinarith [abs_le.mp hright]
  refine ⟨?_,?_⟩
  · intro r hr hra
    exact spectralTurningRegularizedWeight_left h (b n) (eta n) (omega n) (gamma n)
      (d n) (r₀ n-d n*M) r hd hn.2.2.1 hr (hr.trans_le hra) hra hFl hLargeL
  · intro r har
    have ha : 0 < r₀ n+d n*M := by nlinarith [hn.1]
    exact spectralTurningRegularizedWeight_right h (b n) (eta n) (omega n) (gamma n)
      (d n) (r₀ n+d n*M) r hd hn.2.2.1 (ha.trans_le har) ha har hFr hLargeR

end DefocusingNLS

end OAI
