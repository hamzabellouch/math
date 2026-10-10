import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOutgoingFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOutgoingAiry

namespace OAI

/-! The actual outgoing comparison has a nonzero Airy limit. The cutoff is
chosen from the explicit WKB error before extracting a subsequence. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_outgoing_airy_nonzero
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ (M : ℝ) (q : ℕ → ℝ → ℂ × ℂ) (φ : ℕ → ℕ) (p : ℝ → ℂ × ℂ),
      32 ≤ M ∧ StrictMono φ ∧ Continuous p ∧
      (∀ᶠ n in atTop, Continuous (q n) ∧
        q n (E n) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
        spectralScalarFlux (q n (E n)) = h ∧
        ∀ t ∈ Icc R (E n), HasDerivAt (q n) (spectralScalarField
          ((homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+Complex.I*(gamma n : ℂ))
          (q n t)) t) ∧
      (∀ t, -M ≤ t → HasDerivAt p (spectralScalarField (-(t : ℂ)) (p t)) t) ∧
      spectralTurningFluxBase/2 ≤ -h*spectralScalarFlux (p 1) ∧
      ∀ c : ℝ, TendstoUniformlyOn
        (fun n => spectralTurningAiryState (r₀ (φ n)) (d (φ n))
          (Real.sqrt (d (φ n))) (q (φ n))) p atTop (Icc (-M) c) := by
  obtain ⟨M,hM,hflux⟩ := spectralTurning_eventual_outgoing_flux ell h b omega gamma r₀ d E R
    hh hr₀ hdata
  obtain ⟨q,φ,p,hφ,hp,hq,hpD,hlim⟩ := spectralTurning_outgoing_airy_limit ell h b omega gamma r₀ d E M R
    hh hM hR hr₀ hdata
  have hqflux := hflux q (hq.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.2⟩))
  have hpflux : spectralTurningFluxBase/2 ≤ -h*spectralScalarFlux (p (-M)) := by
    apply ge_of_tendsto ((spectralScalarFlux_continuous.continuousAt.tendsto.comp
      ((hlim (-M)).tendsto_at ⟨le_rfl,le_rfl⟩)).const_mul (-h))
    filter_upwards [hφ.tendsto_atTop.eventually hqflux,hφ.tendsto_atTop.eventually hdata] with n hn hdn
    have hdp : 0 < d (φ n) := by
      apply lt_of_le_of_ne hdn.2.1
      intro he
      have hs := hdn.2.2.2.2.2.2.2.2
      rw [← he] at hs
      norm_num at hs
    dsimp only [Function.comp_def]
    rw [spectralTurningAiryState_flux _ _ _ _ (Real.sqrt_pos.mpr hdp).ne']
    have he : r₀ (φ n)-d (φ n)*(-M) = r₀ (φ n)+M*d (φ n) := by ring
    rw [he]
    nlinarith
  have heq := spectralScalarFlux_const (-M) 1 p (fun t => -t) hp.continuousOn
    (fun t ht => by simpa only [Complex.ofReal_neg] using hpD t ht.1.le)
    1 ⟨by linarith,le_rfl⟩
  refine ⟨M,q,φ,p,hM,hφ,hp,hq,hpD,?_,hlim⟩
  simpa only [heq] using hpflux

end DefocusingNLS

end OAI
