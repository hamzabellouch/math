import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningAiryNonzero
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningPhysicalMargin

namespace OAI

/-! Actual normalized outgoing solutions cross the turning region with a
uniformly nonzero physical growing WKB coefficient. No Airy solution or
matching coefficient is assumed as input. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_outgoing_growing_connection
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
      ∀ᶠ T : ℝ in atTop, ∀ᶠ n in atTop,
        let c := r₀ (φ n)-d (φ n)*T
        let P := spectralLiouvilleMomentum (-1) h (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (gamma (φ n)) c
        let D := ((Complex.sqrt P)⁻¹,
          (P+(spectralLiouvilleSlope ((ell (φ n) : ℝ)*(ell (φ n)+10)) c : ℂ)/(4*P^2))*
            (Complex.sqrt P)⁻¹)
        (1/8 : ℝ)*spectralShellNorm (Real.sqrt ‖P‖) (q (φ n) c) ≤
          ‖spectralScalarWronskian D (q (φ n) c)/(-2)‖ := by
  obtain ⟨M,q,φ,p,hM,hφ,hp,hq,hpD,hflux,hlim⟩ := spectralTurning_outgoing_airy_nonzero
    ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  have hpJ : spectralScalarFlux (p 1) ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hflux
    exact (not_le_of_gt (half_pos spectralTurningFluxBase_pos)) hflux
  have hsample : ∀ᶠ n in atTop, 0 < r₀ (φ n) ∧ 0 ≤ d (φ n) ∧
      0 ≤ (ell (φ n) : ℝ)*(ell (φ n)+10) ∧ |gamma (φ n)| ≤ 8 ∧
      homogeneousSpectralLocalizationFrequency h (b (φ n))
        ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (r₀ (φ n)) = 0 ∧
      (r₀ (φ n)/8+2*((ell (φ n) : ℝ)*(ell (φ n)+10)+99/4)/(r₀ (φ n))^3)*(d (φ n))^3 = 1 := by
    filter_upwards [hφ.tendsto_atTop.eventually hdata] with n hn
    exact ⟨hn.1,hn.2.1,by positivity,hn.2.2.2.2.1,
      hn.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2⟩
  refine ⟨q,φ,hφ,hq,?_⟩
  exact spectralTurning_physical_growing_margin h (fun n => b (φ n))
    (fun n => (ell (φ n) : ℝ)*(ell (φ n)+10)) (fun n => omega (φ n))
    (fun n => gamma (φ n)) (fun n => r₀ (φ n)) (fun n => d (φ n)) (-M) 8
    (by linarith) (hr₀.comp hφ.tendsto_atTop) hsample (fun n => q (φ n)) p hp hpD hpJ hlim

end DefocusingNLS

end OAI
