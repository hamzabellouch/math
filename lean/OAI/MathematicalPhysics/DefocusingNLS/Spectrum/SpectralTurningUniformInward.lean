import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningUniformSlope
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRobinCoercive

namespace OAI

/-! Every normalized outgoing scalar comparison has a strictly inward
logarithmic slope on a fixed inner sphere along an escaping turn. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_normalized_uniform_inward
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R B : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hRB : R ≤ B) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᶠ n in atTop,
      ∀ L ∈ Icc R B, ∀ U : ℝ → ℂ × ℂ, ContinuousOn U (Icc L (E (φ n))) →
      (∀ r ∈ Icc L (E (φ n)), HasDerivAt U (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r : ℂ)+Complex.I*(gamma (φ n) : ℂ))
        (U r)) r) →
      U (E (φ n)) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
        (homogeneousSpectralLocalizationFrequency h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (E (φ n))))) →
      ((U L).2/(U L).1).re ≤ -(1/24 : ℝ)*‖spectralLiouvilleMomentum (-1) h (b (φ n))
        ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) L‖ := by
  obtain ⟨φ,hφ,hslope⟩ := spectralTurning_normalized_uniform_slope
    ell h b omega gamma r₀ d E R B hh hR hRB hr₀ hdata
  refine ⟨φ,hφ,?_⟩
  filter_upwards [hslope (1/2) (by norm_num),hφ.tendsto_atTop.eventually hdata,
    (hr₀.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop (max (2*B) (64/R)))]
    with n hsn hdn hlarge
  intro L hL U hUc hUD hUE
  obtain ⟨hU0,hUn⟩ := hsn L hL U hUc hUD hUE
  have hL0 : 0 < L := hR.trans_le hL.1
  change max (2*B) (64/R) ≤ r₀ (φ n) at hlarge
  have hRh : L ≤ r₀ (φ n)/2 := by linarith [(le_max_left (2*B) (64/R)).trans hlarge,hL.2]
  have h64 : 64 ≤ r₀ (φ n)*R := by
    have hh := mul_le_mul_of_nonneg_right ((le_max_right (2*B) (64/R)).trans hlarge) hR.le
    rwa [div_mul_cancel₀ _ hR.ne'] at hh
  have h64L : 64 ≤ r₀ (φ n)*L := h64.trans (mul_le_mul_of_nonneg_left hL.1 hdn.1.le)
  apply spectralTurning_inner_robin_coercive h (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
    (omega (φ n)) (gamma (φ n)) (r₀ (φ n)) L (by positivity) hdn.1 hL0 hRh h64L
    hdn.2.2.2.2.2.2.2.1 (U L) hU0
  let p := spectralLiouvilleMomentum (-1) h (b (φ n))
    ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) L
  let c := p-(spectralLiouvilleSlope ((ell (φ n) : ℝ)*(ell (φ n)+10)) L : ℂ)/(4*p^2)
  change ‖(U L).2+c*(U L).1‖ ≤ (1/2 : ℝ)*‖p‖*‖(U L).1‖
  rw [show (U L).2+c*(U L).1 = ((U L).2/(U L).1+c)*(U L).1 by field_simp [hU0]]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hUn (norm_nonneg _)

end DefocusingNLS

end OAI
