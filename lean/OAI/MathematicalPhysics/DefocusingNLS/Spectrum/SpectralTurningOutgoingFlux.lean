import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningFluxCoarse
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningCutoffChoice

namespace OAI

/-! A single oscillatory cutoff retains a positive amount of the outgoing
flux for every sufficiently large member of the actual parameter family. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_eventual_outgoing_flux
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R : ℝ)
    (hh : h^2 = 1) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ M : ℝ, 32 ≤ M ∧ ∀ q : ℕ → ℝ → ℂ × ℂ,
      (∀ᶠ n in atTop, Continuous (q n) ∧
        q n (E n) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
        ∀ t ∈ Icc R (E n), HasDerivAt (q n) (spectralScalarField
          ((homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+Complex.I*(gamma n : ℂ))
          (q n t)) t) →
      ∀ᶠ n in atTop, spectralTurningFluxBase/2 ≤
        h*spectralScalarFlux (q n (r₀ n+M*d n)) := by
  have hs : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧
      0 ≤ (ell n : ℝ)*(ell n+10) ∧
      (r₀ n/8+2*((ell n : ℝ)*(ell n+10)+99/4)/(r₀ n)^3)*(d n)^3 = 1 := by
    filter_upwards [hdata] with n hn
    exact ⟨hn.1,hn.2.1,by positivity,hn.2.2.2.2.2.2.2.2⟩
  have hd := spectralTurningScale_tendsto (fun n => (ell n : ℝ)*(ell n+10)) r₀ d hr₀ hs
  have hEt : Tendsto E atTop atTop := by
    rw [tendsto_atTop]
    intro A
    filter_upwards [hdata,hr₀.eventually (eventually_ge_atTop (A/2))] with n hn hrn
    linarith [hn.2.2.2.2.2.1]
  obtain ⟨M,hM,hcut⟩ := spectralTurning_cutoff_choice spectralTurningFluxErrorConstant
    spectralTurningFluxRemoteConstant spectralTurningFluxNormConstant spectralTurningFluxBase
    spectralTurningFluxBase_pos r₀ d E hr₀ hd hEt
    (hdata.mono (fun n hn => ⟨hn.1.le,hn.2.1⟩))
  refine ⟨M,hM,?_⟩
  intro q hq
  filter_upwards [hdata,hq,hcut,hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hr₀.eventually (eventually_ge_atTop (max 16 (max R M)))] with n hn hqn hcn hdn hrn
  rcases hn with ⟨hrp,hdn0,hbn,hbn1,hgn,hEn,hEs,hzn,hscn⟩
  have hr16 : 16 ≤ r₀ n := (le_max_left 16 (max R M)).trans hrn
  have hrRM := (le_max_right 16 (max R M)).trans hrn
  have hrr : R ≤ r₀ n := (le_max_left R M).trans hrRM
  have hrM : M ≤ r₀ n := (le_max_right R M).trans hrRM
  have hdp : 0 < d n := by
    apply lt_of_le_of_ne hdn0
    intro he
    rw [← he] at hscn
    norm_num at hscn
  have hmd : M*d n ≤ r₀ n := by nlinarith
  have hlo := spectralTurning_outgoing_flux_lower (ell n) h (b n) (omega n) (gamma n)
    (r₀ n) (d n) M (E n) hh hbn hbn1 hr16 hdp hM hmd hEn hEs hgn hzn hscn
    (q n) hqn.1.continuousOn hqn.2.1
    (fun t ht => hqn.2.2 t ⟨by nlinarith [ht.1],ht.2.le⟩)
  have hcoarse := spectralTurning_flux_coarse (gamma n)
    (spectralTurningOuterError M (r₀ n) (d n)) (E n) hgn hcn.1 hcn.2.1
  apply hcn.2.2.trans
  apply hcoarse.trans
  simpa only [spectralTurningOuterError,spectralTurningCutoffError] using hlo

end DefocusingNLS

end OAI
