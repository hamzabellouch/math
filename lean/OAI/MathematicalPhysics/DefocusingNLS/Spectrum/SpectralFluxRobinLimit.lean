import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxRobin

namespace OAI

/-! Continuity of the weighted flux boundary matrix at a fixed radius. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralFluxBoundary_tendsto (R : ℝ) (μ A : ℕ → ℝ) (μ₀ A₀ : ℝ)
    (M : ℕ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (M₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hA : Tendsto A atTop (𝓝 A₀))
    (hM : Tendsto M atTop (𝓝 M₀)) :
    Tendsto (fun n => spectralFluxBoundary R (μ n) (A n) (M n)) atTop
      (𝓝 (spectralFluxBoundary R μ₀ A₀ M₀)) := by
  have hμc := Complex.continuous_ofReal.continuousAt.tendsto.comp hμ
  have hAc := Complex.continuous_ofReal.continuousAt.tendsto.comp hA
  exact ((hμc.smul hM).sub (hAc.smul tendsto_const_nhds)).const_smul ((R : ℂ)^11)

theorem spectralGaugeFluxBoundary_tendsto (R : ℝ) (μ A : ℕ → ℝ) (μ₀ A₀ : ℝ)
    (q dq : ℕ → ℂ) (q₀ dq₀ : ℂ)
    (M : ℕ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (M₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hA : Tendsto A atTop (𝓝 A₀))
    (hq : Tendsto q atTop (𝓝 q₀)) (hdq : Tendsto dq atTop (𝓝 dq₀))
    (hM : Tendsto M atTop (𝓝 M₀)) (hne : q₀ ≠ 0) :
    Tendsto (fun n => spectralFluxBoundary R (μ n) (A n)
      (spectralGaugeRobin (q n) (dq n) (M n))) atTop
      (𝓝 (spectralFluxBoundary R μ₀ A₀ (spectralGaugeRobin q₀ dq₀ M₀))) :=
  spectralFluxBoundary_tendsto R μ A μ₀ A₀ _ _ hμ hA
    (spectralGaugeRobin_tendsto q dq q₀ dq₀ M M₀ hq hdq hM hne)

end DefocusingNLS

end OAI
