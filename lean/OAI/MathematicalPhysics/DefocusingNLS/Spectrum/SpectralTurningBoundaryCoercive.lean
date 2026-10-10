import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningBoundarySlope
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRobinCoercive

namespace OAI

/-! Every normalized outgoing scalar comparison has a strictly inward
logarithmic slope on a fixed inner sphere along an escaping turn. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_normalized_inward
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᶠ n in atTop,
      ∀ U : ℝ → ℂ × ℂ, ContinuousOn U (Icc R (E (φ n))) →
      (∀ r ∈ Icc R (E (φ n)), HasDerivAt U (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r : ℂ)+Complex.I*(gamma (φ n) : ℂ))
        (U r)) r) →
      U (E (φ n)) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
        (homogeneousSpectralLocalizationFrequency h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (E (φ n))))) →
      ((U R).2/(U R).1).re ≤ -(1/24 : ℝ)*‖spectralLiouvilleMomentum (-1) h (b (φ n))
        ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) R‖ := by
  obtain ⟨φ,hφ,hslope⟩ := spectralTurning_normalized_slope
    ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  refine ⟨φ,hφ,?_⟩
  filter_upwards [hslope (1/2) (by norm_num),hφ.tendsto_atTop.eventually hdata,
    (hr₀.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop (max (2*R) (64/R)))]
    with n hsn hdn hlarge
  intro U hUc hUD hUE
  obtain ⟨hU0,hUn⟩ := hsn U hUc hUD hUE
  change max (2*R) (64/R) ≤ r₀ (φ n) at hlarge
  have hRh : R ≤ r₀ (φ n)/2 := by linarith [(le_max_left (2*R) (64/R)).trans hlarge]
  have h64 : 64 ≤ r₀ (φ n)*R := by
    have hh := mul_le_mul_of_nonneg_right ((le_max_right (2*R) (64/R)).trans hlarge) hR.le
    rwa [div_mul_cancel₀ _ hR.ne'] at hh
  apply spectralTurning_inner_robin_coercive h (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
    (omega (φ n)) (gamma (φ n)) (r₀ (φ n)) R (by positivity) hdn.1 hR hRh h64
    hdn.2.2.2.2.2.2.2.1 (U R) hU0
  let p := spectralLiouvilleMomentum (-1) h (b (φ n))
    ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) R
  let c := p-(spectralLiouvilleSlope ((ell (φ n) : ℝ)*(ell (φ n)+10)) R : ℂ)/(4*p^2)
  change ‖(U R).2+c*(U R).1‖ ≤ (1/2 : ℝ)*‖p‖*‖(U R).1‖
  rw [show (U R).2+c*(U R).1 = ((U R).2/(U R).1+c)*(U R).1 by field_simp [hU0]]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hUn (norm_nonneg _)

end DefocusingNLS

end OAI
