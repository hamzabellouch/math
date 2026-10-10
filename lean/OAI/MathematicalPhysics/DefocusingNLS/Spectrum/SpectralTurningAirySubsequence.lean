import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningAiryHalfLineLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningDataBound
import Mathlib.Topology.Sequences

namespace OAI

/-! Compact rescaled outgoing data produce one limiting Airy solution and a
single subsequence on all fixed observation intervals. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurningAiry_subsequence
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (M R G C : ℝ) (hM : 0 < M)
    (q : ℕ → ℝ → ℂ × ℂ) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8 + 2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1)
    (hq : ∀ᶠ n in atTop, Continuous (q n) ∧ ∀ r ∈ Icc R (2*r₀ n),
      HasDerivAt (q n) (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) r : ℂ) +
          Complex.I*(gamma n : ℂ)) (q n r)) r)
    (hbound : ∀ᶠ n in atTop, spectralShellNorm
      (Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n) (eta n) (omega n) (gamma n)
        (r₀ n+d n*M)‖) (q n (r₀ n+d n*M)) ≤ C) :
    ∃ (φ : ℕ → ℕ) (p : ℝ → ℂ × ℂ), StrictMono φ ∧ Continuous p ∧
      (∀ t, -M ≤ t → HasDerivAt p (spectralScalarField (-(t : ℂ)) (p t)) t) ∧
      ∀ c : ℝ, TendstoUniformlyOn
        (fun n => spectralTurningAiryState (r₀ (φ n)) (d (φ n))
          (Real.sqrt (d (φ n))) (q (φ n))) p atTop (Icc (-M) c) := by
  obtain ⟨B,hB⟩ := spectralTurning_rescaled_data_bounded h b eta omega gamma r₀ d M G C
    hM q hr₀ hdata hbound
  let v := fun n => spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n) (-M)
  have hmem : ∀ᶠ n in atTop, v n ∈ Metric.closedBall (0 : ℂ × ℂ) B := by
    filter_upwards [hB] with n hn
    simpa only [Metric.mem_closedBall,dist_zero_right] using hn
  obtain ⟨x,_,φ,hφ,hx⟩ := (isCompact_closedBall (0 : ℂ × ℂ) B).tendsto_subseq' hmem.frequently
  obtain ⟨p,hp,_,hpD,hlim⟩ := spectralTurningAiry_halfLine_limit h
    (fun n => b (φ n)) (fun n => eta (φ n)) (fun n => omega (φ n))
    (fun n => gamma (φ n)) (fun n => r₀ (φ n)) (fun n => d (φ n))
    (-M) R G (fun n => q (φ n)) x (hr₀.comp hφ.tendsto_atTop)
    (hφ.tendsto_atTop.eventually hdata) (hφ.tendsto_atTop.eventually hq) hx
  exact ⟨φ,p,hφ,hp,hpD,hlim⟩

end DefocusingNLS

end OAI
