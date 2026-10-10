import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnRadiusOrder

namespace OAI

/-! Uniform outgoing slope control over a fixed shell. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralNoTurn_eventual_uniform_slope
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ) (C R B : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (_hRB : R ≤ B) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ |gamma n| ≤ 8 ∧ 0 < E n ∧
      (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    ∀ᶠ n in atTop, ∀ L ∈ Icc R B, ∀ U : ℝ → ℂ × ℂ,
      ContinuousOn U (Icc L (E n)) →
      U (E n) = spectralOscillatoryData (-1) (Real.sqrt (Real.sqrt
        (homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) →
      (∀ t ∈ Ioo L (E n), HasDerivAt U (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+
          Complex.I*(gamma n : ℂ)) (U t)) t) →
      (U L).1 ≠ 0 ∧
      ‖((U L).2/(U L).1)/(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) L) : ℂ)+Complex.I‖ ≤
        spectralNoTurnRealError C R (omega n) (E n) := by
  obtain ⟨hE,hp⟩ := spectralNoTurn_eventual_data ell b omega gamma E C R hC hR hw hdata
  filter_upwards [hdata,hp,hw.eventually (eventually_ge_atTop (16 : ℝ)),
    hE.eventually (eventually_ge_atTop B)] with n hn hpn h16 hBE
  intro L hL U hUc hUE hUD
  have hL0 : 0 < L := hR.trans_le hL.1
  have hLE : L ≤ E n := hL.2.trans hBE
  have hCL : 2*C ≤ L^2 := hCR.trans (pow_le_pow_left₀ hR.le hL.1 2)
  have hKL := (spectralNoTurn_derivative_radius_mono C R L hC hR hL.1).trans hpn.2.2.2.2.2.1
  have herrL := (spectralNoTurn_branch_radius_mono C R L (omega n) (E n) hC hR hL.1).trans hpn.2.2.2.2.2.2
  let eta := (ell n : ℝ)*(ell n+10)
  let F := homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) L
  let p := spectralLiouvilleMomentum 1 (-1) (b n) eta (omega n) (gamma n) L
  let K := 2/L+4*C/L^3
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hFlo : omega n/2 ≤ F := by
    have hh := spectralNoTurn_frequency_lower (b n) eta (omega n) C L L
      hn.1 hpn.1 hL0 le_rfl hn.2.2.2.1 hCL
    dsimp only [F]
    nlinarith [sq_nonneg L]
  have hF : 0 < F := (half_pos hpn.1).trans_le hFlo
  have hgF : |gamma n| ≤ F := hn.2.1.trans (by linarith)
  have hgE : |gamma n| ≤ homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) (E n) := by
    have hh := spectralNoTurn_frequency_lower (b n) eta (omega n) C L (E n)
      hn.1 hpn.1 hL0 hLE hn.2.2.2.1 hCL
    nlinarith [hn.2.1,sq_nonneg (E n)]
  have hl := spectralNoTurn_outgoing_logarithmic_bound (b n) eta (omega n) (gamma n) C L (E n)
    hn.1 heta hpn.1 hC hpn.2.1 hL0 hLE hn.2.2.1 hpn.2.2.2.1 hn.2.2.2.1 hCL
    hn.2.1 hpn.2.2.2.2.1 hKL hgE herrL U hUc hUE hUD
  let eps := 5*spectralNoTurnBranchError C L (omega n) (E n)/Real.exp (-256)+K/(4*‖p‖)
  have heps : 0 ≤ eps := (norm_nonneg _).trans hl.2
  have hreal := spectralPositiveMomentum_ratio_error F (gamma n) eps
    ((U L).2/(U L).1) hF hgF heps (by
      simpa only [eps,K,p,F,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul] using hl.2)
  have hpnorm : Real.sqrt (omega n/2) ≤ ‖p‖ :=
    spectralNoTurn_momentum_lower (b n) eta (omega n) (gamma n) C L L
      hn.1 hpn.1 hL0 le_rfl hn.2.2.2.1 hCL
  have hc : K/(4*‖p‖) ≤ K/(4*Real.sqrt (omega n/2)) :=
    div_le_div_of_nonneg_left hK (by positivity) (by linarith)
  have hg : |gamma n|/F ≤ 16/omega n := by
    calc
      _ ≤ 8/(omega n/2) := div_le_div₀ (by norm_num) hn.2.1 (half_pos hpn.1) hFlo
      _ = _ := by ring
  refine ⟨hl.1,le_trans (hreal.trans ?_)
    (spectralNoTurn_real_radius_mono C R L (omega n) (E n) hC hR hL.1)⟩
  dsimp only [spectralNoTurnRealError,eps,K] at *
  linarith

end DefocusingNLS

end OAI
