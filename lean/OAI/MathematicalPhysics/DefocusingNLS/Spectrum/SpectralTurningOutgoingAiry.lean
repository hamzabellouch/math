import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOutgoingFamily
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningAirySubsequence

namespace OAI

/-! Construct the scalar outgoing comparison family and extract its actual
Airy limit along one subsequence. No compactness hypothesis on the Cauchy
data is supplied: the outgoing transfer bound proves it. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_outgoing_airy_limit
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (M R : ℝ)
    (hh : h^2 = 1) (hM : 32 ≤ M) (hR : 0 < R)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ (q : ℕ → ℝ → ℂ × ℂ) (φ : ℕ → ℕ) (p : ℝ → ℂ × ℂ),
      StrictMono φ ∧ Continuous p ∧
      (∀ᶠ n in atTop, Continuous (q n) ∧
        q n (E n) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
        spectralScalarFlux (q n (E n)) = h ∧
        ∀ t ∈ Icc R (E n), HasDerivAt (q n) (spectralScalarField
          ((homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ) + Complex.I*(gamma n : ℂ))
          (q n t)) t) ∧
      (∀ t, -M ≤ t → HasDerivAt p (spectralScalarField (-(t : ℂ)) (p t)) t) ∧
      ∀ c : ℝ, TendstoUniformlyOn
        (fun n => spectralTurningAiryState (r₀ (φ n)) (d (φ n))
          (Real.sqrt (d (φ n))) (q (φ n))) p atTop (Icc (-M) c) := by
  obtain ⟨q,hq⟩ := spectralTurning_outgoing_family ell h b omega gamma r₀ d E M R
    hh hM hR hr₀ hdata
  have hd : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ (ell n : ℝ)*(ell n+10) ∧
      |gamma n| ≤ 8 ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8 + 2*((ell n : ℝ)*(ell n+10)+99/4)/(r₀ n)^3)*(d n)^3 = 1 := by
    filter_upwards [hdata] with n hn
    exact ⟨hn.1,hn.2.1,by positivity,hn.2.2.2.2.1,
      hn.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2⟩
  have hqc : ∀ᶠ n in atTop, Continuous (q n) ∧ ∀ t ∈ Icc R (2*r₀ n),
      HasDerivAt (q n) (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ) + Complex.I*(gamma n : ℂ))
        (q n t)) t := by
    filter_upwards [hdata,hq] with n hn hqn
    exact ⟨hqn.1,fun t ht => hqn.2.2.2.2 t ⟨ht.1,ht.2.trans hn.2.2.2.2.2.1⟩⟩
  have hqb : ∀ᶠ n in atTop, spectralShellNorm
      (Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n) ((ell n : ℝ)*(ell n+10))
        (omega n) (gamma n) (r₀ n+d n*M)‖) (q n (r₀ n+d n*M)) ≤
      (75/2 : ℝ)*Real.exp (8*288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+11)) := by
    filter_upwards [hq] with n hn
    simpa only [mul_comm (d n) M] using hn.2.2.2.1
  obtain ⟨φ,p,hφ,hp,hpD,hlim⟩ := spectralTurningAiry_subsequence h b
    (fun n => (ell n : ℝ)*(ell n+10)) omega gamma r₀ d M R 8
    ((75/2 : ℝ)*Real.exp (8*288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+11)))
    (by linarith) q hr₀ hd hqc hqb
  refine ⟨q,φ,p,hφ,hp,?_,hpD,hlim⟩
  exact hq.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2⟩)

end DefocusingNLS

end OAI
