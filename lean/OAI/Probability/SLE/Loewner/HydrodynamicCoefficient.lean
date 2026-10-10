import OAI.Probability.SLE.Loewner.HydrodynamicHeight

namespace OAI

/-! A height-decreasing half-plane chart has nonnegative hydrodynamic
coefficient. The argument uses the actual Laurent limit on the imaginary axis. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

lemma hydrodynamic_coefficient_nonneg {G : ℂ → ℂ} {c : ℝ}
    (hc : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 (c:ℂ)))
    (hheight : ∀ᶠ z in cocompact ℂ ⊓ 𝓟 upperHalfPlane, (G z).im ≤ z.im) : 0≤c := by
  have hv := verticalInfinity_tendsto
  have hr := Complex.continuous_re.tendsto (c:ℂ) |>.comp (hc.comp (hv.mono_right inf_le_left))
  have hn : ∀ᶠ n in atTop, 0 ≤ (verticalInfinity n*(G (verticalInfinity n)-verticalInfinity n)).re := by
    filter_upwards [hv.eventually hheight] with n hn
    have hy : 0 < (n:ℝ)+1 := by positivity
    simp only [verticalInfinity,mul_im,mul_re,ofReal_re,ofReal_im,I_re,I_im,mul_zero,
      add_zero,mul_one,sub_im,sub_re,zero_sub] at hn ⊢
    nlinarith
  have hh : 0 ≤ (c:ℂ).re := ge_of_tendsto hr (by
    simpa only [Function.comp_apply] using hn)
  simpa only [ofReal_re] using hh

lemma normalized_inverse_height
    {D : Set ℂ} {G F : ℂ → ℂ}
    (hG : MapsTo G D upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane) (hmap : MapsTo F upperHalfPlane upperHalfPlane)
    (hleft : ∀ z ∈ D, F (G z)=z)
    (hn : Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1)) :
    ∀ z ∈ D, (G z).im ≤ z.im := by
  intro z hz
  have hh := normalized_halfPlane_height hF hmap hn (hG hz)
  rwa [hleft z hz] at hh

end SLEExactGauge

end

end OAI
