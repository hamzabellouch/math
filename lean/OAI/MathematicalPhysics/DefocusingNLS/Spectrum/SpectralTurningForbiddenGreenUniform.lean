import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningForbiddenGreen
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningResidualUniform

namespace OAI

/-! The forbidden Green bound has a constant independent of the escaping
parameters, after selecting the fixed turning cutoff. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_outgoing_forbidden_green_uniform
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
      ∃ M : ℝ, 32 ≤ M ∧ ∀ᶠ n in atTop,
        let c := r₀ (φ n)-M*d (φ n)
        let p := spectralLiouvilleMomentum (-1) h (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (gamma (φ n))
        let k := fun t => Real.sqrt ‖p t‖
        ∃ (D : ℝ → ℂ × ℂ) (W : ℂ), Continuous D ∧ D R = (0,(k R : ℂ)) ∧
          (∀ t ∈ Icc R c, HasDerivAt D (spectralScalarField
            ((homogeneousSpectralLocalizationFrequency h (b (φ n))
              ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) t : ℂ)+
                Complex.I*(gamma (φ n) : ℂ)) (D t)) t) ∧
          W ≠ 0 ∧ (∀ t ∈ Icc R c, spectralScalarWronskian (D t) (q (φ n) t) = W) ∧
          ∀ r ∈ Icc R c, ∀ t ∈ Icc R c,
            spectralShellNorm (k r) (spectralScalarGreenState D (q (φ n)) W r t) ≤
              1250*Real.exp 4/(k t) := by
  obtain ⟨q,φ,hφ,hq,M,hM,hgreen⟩ := spectralTurning_outgoing_forbidden_green
    ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  let eta := fun n => (ell (φ n) : ℝ)*(ell (φ n)+10)
  have hsample : ∀ᶠ n in atTop, 0 < r₀ (φ n) ∧ 0 ≤ d (φ n) ∧ 0 ≤ eta n ∧
      homogeneousSpectralLocalizationFrequency h (b (φ n)) (eta n) (omega (φ n)) (r₀ (φ n)) = 0 ∧
      spectralLiouvilleSlope (eta n) (r₀ (φ n))*(d (φ n))^3 = 1 := by
    filter_upwards [hφ.tendsto_atTop.eventually hdata] with n hn
    exact ⟨hn.1,hn.2.1,by dsimp only [eta]; positivity,
      hn.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2⟩
  have hres := spectralTurning_eventual_residual_bound h (fun n => b (φ n)) eta
    (fun n => omega (φ n)) (fun n => gamma (φ n)) (fun n => r₀ (φ n))
    (fun n => d (φ n)) R M hR hM (hr₀.comp hφ.tendsto_atTop) hsample
  refine ⟨q,φ,hφ,hq,M,hM,?_⟩
  filter_upwards [hgreen,hres] with n hgn hrn
  obtain ⟨D,W,hDc,hDR,hDD,hW,hdet,hbound⟩ := hgn
  refine ⟨D,W,hDc,hDR,hDD,hW,hdet,?_⟩
  intro r hr t ht
  apply (hbound r hr t ht).trans
  gcongr
  linarith

end DefocusingNLS

end OAI
