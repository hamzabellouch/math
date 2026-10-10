import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningUniformLimit

namespace OAI

/-! The reflected coefficient converges to the Airy coefficient on every
fixed compact interval, with no symmetry restriction on its endpoints. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurningAiryCoefficient_uniform_limit
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (a c G : ℝ)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8 + 2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1) :
    TendstoUniformlyOn
      (fun n t => spectralTurningCoefficient h (b n) (eta n) (omega n)
        (gamma n) (r₀ n) (d n) (-t))
      (fun t => -(t : ℂ)) atTop (Icc a c) := by
  let M := max |a| |c|
  have hM : 0 ≤ M := (abs_nonneg a).trans (le_max_left _ _)
  have ha : -M ≤ a := (neg_le_neg (le_max_left |a| |c|)).trans (neg_abs_le a)
  have hc : c ≤ M := (le_abs_self c).trans (le_max_right _ _)
  have hu := spectralTurningCoefficient_uniform_limit h b eta omega gamma r₀ d M G hM hr₀ hdata
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) eps heps] with n hn t ht
  have hm : -t ∈ Icc (-M) M := by constructor <;> linarith [ht.1,ht.2]
  simpa only [Complex.ofReal_neg] using hn (-t) hm

end DefocusingNLS

end OAI
