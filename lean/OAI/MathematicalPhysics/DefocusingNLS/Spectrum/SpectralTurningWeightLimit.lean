import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaledNorm
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningUniformLimit

namespace OAI

/-! The physical WKB weight becomes the fixed Airy weight after rescaling. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_weight_tendsto
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (M G : ℝ) (hM : 0 ≤ M)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8 + 2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1) :
    Tendsto (fun n => Real.sqrt (d n) * Real.sqrt ‖spectralLiouvilleMomentum 1 h
      (b n) (eta n) (omega n) (gamma n) (r₀ n+d n*M)‖)
      atTop (𝓝 (Real.sqrt (Real.sqrt M))) := by
  have hu := (spectralTurningCoefficient_uniform_limit h b eta omega gamma r₀ d M G hM
    hr₀ hdata).tendsto_at (show M ∈ Icc (-M) M from ⟨by linarith,le_rfl⟩)
  have hk := (Real.continuous_sqrt.tendsto _).comp
    ((Real.continuous_sqrt.tendsto _).comp hu.norm)
  have hk' : Tendsto (fun n => Real.sqrt (Real.sqrt
      ‖spectralTurningCoefficient h (b n) (eta n) (omega n) (gamma n) (r₀ n) (d n) M‖))
      atTop (𝓝 (Real.sqrt (Real.sqrt M))) := by
    simpa only [Function.comp_def,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM] using hk
  apply hk'.congr'
  filter_upwards [hdata] with n hn
  exact (spectralTurning_scaled_weight h (b n) (eta n) (omega n) (gamma n)
    (r₀ n) (d n) M hn.2.1).symm


theorem spectralTurning_weight_tendsto_at
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (xi G : ℝ)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8 + 2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1) :
    Tendsto (fun n => Real.sqrt (d n) * Real.sqrt ‖spectralLiouvilleMomentum 1 h
      (b n) (eta n) (omega n) (gamma n) (r₀ n+d n*xi)‖)
      atTop (𝓝 (Real.sqrt (Real.sqrt |xi|))) := by
  have hu := (spectralTurningCoefficient_uniform_limit h b eta omega gamma r₀ d |xi| G
    (abs_nonneg xi) hr₀ hdata).tendsto_at
      (show xi ∈ Icc (-|xi|) |xi| from ⟨neg_abs_le xi,le_abs_self xi⟩)
  have hk := (Real.continuous_sqrt.tendsto _).comp
    ((Real.continuous_sqrt.tendsto _).comp hu.norm)
  have hk' : Tendsto (fun n => Real.sqrt (Real.sqrt
      ‖spectralTurningCoefficient h (b n) (eta n) (omega n) (gamma n) (r₀ n) (d n) xi‖))
      atTop (𝓝 (Real.sqrt (Real.sqrt |xi|))) := by
    simpa only [Function.comp_def,Complex.norm_real,Real.norm_eq_abs] using hk
  apply hk'.congr'
  filter_upwards [hdata] with n hn
  exact (spectralTurning_scaled_weight h (b n) (eta n) (omega n) (gamma n)
    (r₀ n) (d n) xi hn.2.1).symm

end DefocusingNLS

end OAI
