import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningInnerCone
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRobinCoercive

namespace OAI

/-! The actual scalar outgoing family has a coercive inward Robin slope
along every escaping turning-parameter sequence, after subselection. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_outgoing_robin
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ (q : ℕ → ℝ → ℂ × ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ᶠ n in atTop, Continuous (q n) ∧
        q n (E n) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
        spectralScalarFlux (q n (E n)) = h ∧
        ∀ t ∈ Icc R (E n), HasDerivAt (q n) (spectralScalarField
          ((homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+Complex.I*(gamma n : ℂ))
          (q n t)) t) ∧
      ∀ᶠ n in atTop, (q (φ n) R).1 ≠ 0 ∧
        ((q (φ n) R).2/(q (φ n) R).1).re ≤ -(r₀ (φ n))/384 := by
  obtain ⟨q,φ,hφ,hq,hcone⟩ := spectralTurning_outgoing_inner_cone
    ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  refine ⟨q,φ,hφ,hq,?_⟩
  have hrt := hr₀.comp hφ.tendsto_atTop
  filter_upwards [hcone,hφ.tendsto_atTop.eventually hdata,
    hrt.eventually (eventually_ge_atTop (max (2*R) (64/R)))] with n hn hd hl
  dsimp only [Function.comp_def] at hl
  have hRh : R ≤ r₀ (φ n)/2 := by linarith [le_trans (le_max_left (2*R) (64/R)) hl]
  have hlarge : 64 ≤ r₀ (φ n)*R := by
    have hh := mul_le_mul_of_nonneg_right ((le_max_right (2*R) (64/R)).trans hl) hR.le
    have he : (64/R)*R = 64 := by field_simp
    rwa [he] at hh
  let eta := (ell (φ n) : ℝ)*(ell (φ n)+10)
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  have hz : homogeneousSpectralLocalizationFrequency h (b (φ n)) eta (omega (φ n))
      (r₀ (φ n)) = 0 := hd.2.2.2.2.2.2.2.1
  have hc := spectralTurning_inner_robin_coercive h (b (φ n)) eta (omega (φ n))
    (gamma (φ n)) (r₀ (φ n)) R heta hd.1 hR hRh hlarge hz (q (φ n) R) hn.1 hn.2
  have hp := spectralTurning_far_momentum_re_lower h (b (φ n)) eta (omega (φ n))
    (gamma (φ n)) (r₀ (φ n)) R heta hd.1 hR hRh hz
  have hnorm : (spectralLiouvilleMomentum (-1) h (b (φ n)) eta (omega (φ n))
      (gamma (φ n)) R).re ≤ ‖spectralLiouvilleMomentum (-1) h (b (φ n)) eta
        (omega (φ n)) (gamma (φ n)) R‖ := Complex.re_le_norm _
  refine ⟨hn.1,?_⟩
  -- The real-part bound is deliberately weaker than the modulus bound.
  linarith

end DefocusingNLS

end OAI
