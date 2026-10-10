import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningAiryLimit

namespace OAI

/-! One limiting Airy solution works on every fixed compact interval. Local
uniqueness makes the independently obtained interval limits agree. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurningAiry_halfLine_limit
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (a R G : ℝ)
    (q : ℕ → ℝ → ℂ × ℂ) (x : ℂ × ℂ)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8 + 2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1)
    (hq : ∀ᶠ n in atTop, Continuous (q n) ∧ ∀ r ∈ Icc R (2*r₀ n),
      HasDerivAt (q n) (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) r : ℂ) +
          Complex.I*(gamma n : ℂ)) (q n r)) r)
    (hinit : Tendsto (fun n =>
      spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n) a) atTop (𝓝 x)) :
    ∃ p : ℝ → ℂ × ℂ, Continuous p ∧ p a = x ∧
      (∀ t, a ≤ t → HasDerivAt p (spectralScalarField (-(t : ℂ)) (p t)) t) ∧
      ∀ c : ℝ, TendstoUniformlyOn
        (fun n => spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n))
        p atTop (Icc a c) := by
  obtain ⟨p,hp,hpa,hpD,_⟩ := spectralTurningAiry_cauchy_limit h b eta omega gamma r₀ d
    a a R G q x hr₀ hdata hq hinit
  refine ⟨p,hp,hpa,hpD,?_⟩
  intro c
  obtain ⟨u,hu,hua,huD,hlim⟩ := spectralTurningAiry_cauchy_limit h b eta omega gamma r₀ d
    a c R G q x hr₀ hdata hq hinit
  apply hlim.congr_right
  intro t ht
  apply spectralScalar_unique_right a t ht.1 (fun s => -(s : ℂ)) (by fun_prop)
    u p hu.continuousOn hp.continuousOn
  · exact fun s hs => huD s hs.1.le
  · exact fun s hs => hpD s hs.1.le
  · exact hua.trans hpa.symm

end DefocusingNLS

end OAI
