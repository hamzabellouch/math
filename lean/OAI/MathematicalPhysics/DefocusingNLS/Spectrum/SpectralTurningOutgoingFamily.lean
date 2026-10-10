import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOutgoingBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaleLimit

namespace OAI

/-! The normalized scalar outgoing solutions can be chosen along an escaping
parameter sequence with one bound at any fixed oscillatory cutoff. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_outgoing_bound_coarse (M r₀ d gamma : ℝ)
    (hM : 32 ≤ M) (hr₀ : 1 ≤ r₀) (_hd : 0 ≤ d) (hd1 : d ≤ 1) (hg : |gamma| ≤ 8) :
    (75/2 : ℝ)*Real.exp (|gamma| *288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+
      3*d/(r₀*Real.sqrt (M/8))+8/r₀^2)) ≤
    (75/2 : ℝ)*Real.exp (8*288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+11)) := by
  have hMp : 0 ≤ M/8 := by linarith
  have hs : 1 ≤ Real.sqrt (M/8) := by
    nlinarith [Real.sq_sqrt hMp,Real.sqrt_nonneg (M/8)]
  have hp : 0 < r₀*Real.sqrt (M/8) := by positivity
  have hden : 1 ≤ r₀*Real.sqrt (M/8) := by nlinarith
  have hterm : 3*d/(r₀*Real.sqrt (M/8)) ≤ 3 :=
    (div_le_iff₀ hp).mpr (by nlinarith)
  have hfar : 8/r₀^2 ≤ 8 := div_le_self (by norm_num) (by nlinarith)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith

theorem spectralTurning_outgoing_family
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (M R : ℝ)
    (hh : h^2 = 1) (hM : 32 ≤ M) (hR : 0 < R)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ q : ℕ → ℝ → ℂ × ℂ, ∀ᶠ n in atTop, Continuous (q n) ∧
      q n (E n) = spectralOscillatoryData h
        (Real.sqrt (Real.sqrt (homogeneousSpectralLocalizationFrequency h (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
      spectralScalarFlux (q n (E n)) = h ∧
      spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (gamma n) (r₀ n+M*d n)‖)
        (q n (r₀ n+M*d n)) ≤
        (75/2 : ℝ)*Real.exp (8*288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+11)) ∧
      ∀ t ∈ Icc R (E n), HasDerivAt (q n) (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ) + Complex.I*(gamma n : ℂ))
        (q n t)) t := by
  have hscale : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧
      0 ≤ (ell n : ℝ)*(ell n+10) ∧
      (r₀ n/8 + 2*((ell n : ℝ)*(ell n+10)+99/4)/(r₀ n)^3)*(d n)^3 = 1 := by
    filter_upwards [hdata] with n hn
    exact ⟨hn.1,hn.2.1,by positivity,hn.2.2.2.2.2.2.2.2⟩
  have hd := spectralTurningScale_tendsto (fun n => (ell n : ℝ)*(ell n+10)) r₀ d hr₀ hscale
  let valid := fun n => 16 ≤ r₀ n ∧ 0 < d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧ |gamma n| ≤ 8 ∧
    R ≤ r₀ n/2 ∧ M*d n ≤ r₀ n/2 ∧ 2*r₀ n ≤ E n ∧
    (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
    homogeneousSpectralLocalizationFrequency h (b n)
      ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
    spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1
  have hevent : ∀ᶠ n in atTop, valid n ∧ d n ≤ 1 := by
    filter_upwards [hdata,hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hr₀.eventually (eventually_ge_atTop (max 16 (max (2*R) (2*M))))] with n hn hdn hrn
    have hdn0 : 0 < d n := by
      apply lt_of_le_of_ne hn.2.1
      intro he
      have hsc := hn.2.2.2.2.2.2.2.2
      rw [← he] at hsc
      norm_num at hsc
    have hr16 := (le_max_left 16 (max (2*R) (2*M))).trans hrn
    have hrRM := (le_max_right 16 (max (2*R) (2*M))).trans hrn
    have hrR := (le_max_left (2*R) (2*M)).trans hrRM
    have hrM := (le_max_right (2*R) (2*M)).trans hrRM
    refine ⟨⟨hr16,hdn0,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,?_,?_,
      hn.2.2.2.2.2.1,hn.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2⟩,hdn.le⟩
    · linarith
    · nlinarith
  let P := fun n (q : ℝ → ℂ × ℂ) => Continuous q ∧
    q (E n) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
      (homogeneousSpectralLocalizationFrequency h (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
    spectralScalarFlux (q (E n)) = h ∧
    spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n) ((ell n : ℝ)*(ell n+10))
      (omega n) (gamma n) (r₀ n+M*d n)‖) (q (r₀ n+M*d n)) ≤
      (75/2 : ℝ)*Real.exp (|gamma n| *288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+
        3*d n/(r₀ n*Real.sqrt (M/8))+8/(r₀ n)^2)) ∧
    ∀ t ∈ Icc R (E n), HasDerivAt q (spectralScalarField
      ((homogeneousSpectralLocalizationFrequency h (b n) ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ) +
        Complex.I*(gamma n : ℂ)) (q t)) t
  have hex (n : ℕ) : ∃ q : ℝ → ℂ × ℂ, valid n → P n q := by
    by_cases hv : valid n
    · obtain ⟨q,hq⟩ := spectralTurning_outgoing_comparison_bound (ell n) h (b n) (omega n)
        (gamma n) (r₀ n) (d n) M R (E n) hh hv.2.2.1 hv.2.2.2.1 hv.1 hv.2.1 hM
        hR hv.2.2.2.2.2.1 hv.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2.1
        hv.2.2.2.2.2.2.2.2.1 hv.2.2.2.2.1 hv.2.2.2.2.2.2.2.2.2.1
        hv.2.2.2.2.2.2.2.2.2.2
      exact ⟨q,fun _ => hq⟩
    · exact ⟨0,fun hv' => (hv hv').elim⟩
  choose q hq using hex
  refine ⟨q,?_⟩
  filter_upwards [hevent] with n hn
  obtain ⟨hc,hE,hJ,hN,hD⟩ := hq n hn.1
  refine ⟨hc,hE,hJ,hN.trans ?_,hD⟩
  exact spectralTurning_outgoing_bound_coarse M (r₀ n) (d n) (gamma n) hM
    (by linarith [hn.1.1]) hn.1.2.1.le hn.2 hn.1.2.2.2.2.1

end DefocusingNLS

end OAI
