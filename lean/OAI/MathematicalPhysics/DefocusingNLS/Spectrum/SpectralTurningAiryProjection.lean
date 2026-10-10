import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningProjectionLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningAiryState
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAiryGrowingMargin

namespace OAI

/-! Nonzero limiting flux supplies a fixed growing-mode margin for the
actual rescaled WKB projection at every sufficiently late fixed Airy point. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_eventual_growing_projection
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (a G : ℝ) (ha : a ≤ 1)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8+2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1)
    (q : ℕ → ℝ → ℂ × ℂ) (p : ℝ → ℂ × ℂ) (hp : Continuous p)
    (hpD : ∀ t, a ≤ t → HasDerivAt p (spectralScalarField (-(t : ℂ)) (p t)) t)
    (hpJ : spectralScalarFlux (p 1) ≠ 0)
    (hlim : ∀ c : ℝ, TendstoUniformlyOn
      (fun n => spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n)) p atTop (Icc a c)) :
    ∀ᶠ T : ℝ in atTop, ∀ᶠ n in atTop,
      let u := spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n) T
      let P := (d n : ℂ)*spectralLiouvilleMomentum (-1) h (b n) (eta n)
        (omega n) (gamma n) (r₀ n-d n*T)
      let A := ((d n)^3*spectralLiouvilleSlope (eta n) (r₀ n-d n*T) : ℝ)
      (1/8 : ℝ)*spectralShellNorm (Real.sqrt ‖P‖) u ≤
        ‖(u.2+(P+(A : ℂ)/(4*P^2))*u.1)/(2*Complex.sqrt P)‖ := by
  have hmargin := spectralAiry_eventual_growing_margin p 1 le_rfl hp.continuousOn
    (fun t ht => hpD t (ha.trans ht)) hpJ
  filter_upwards [hmargin,eventually_ge_atTop (1 : ℝ)] with T hTmargin hT
  have hTp : 0 < T := by linarith
  have hJT : spectralScalarFlux (p T) ≠ 0 := by
    rw [spectralScalarFlux_const 1 T p (fun t => -t) hp.continuousOn
      (fun t ht => by simpa only [Complex.ofReal_neg] using hpD t (ha.trans ht.1.le))
      T ⟨hT,le_rfl⟩]
    exact hpJ
  exact spectralTurning_growing_projection_margin h b eta omega gamma r₀ d T G hTp hr₀ hdata
    (p T) (fun n => spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n) T)
    hJT ((hlim T).tendsto_at ⟨ha.trans hT,le_rfl⟩) hTmargin

end DefocusingNLS

end OAI
