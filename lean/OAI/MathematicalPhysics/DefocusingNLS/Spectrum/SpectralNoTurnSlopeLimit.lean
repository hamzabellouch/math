import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnLogarithmic
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnEventual
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPositiveMomentum

namespace OAI

/-! The no-turn channel has the precise outgoing slope in the paper's real
frequency normalization, for every normalized terminal solution. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def spectralNoTurnRealError (C R omega E : ℝ) : ℝ :=
  2*(5*spectralNoTurnBranchError C R omega E/Real.exp (-256)+
    (2/R+4*C/R^3)/(4*Real.sqrt (omega/2)))+16/omega

theorem spectralNoTurn_real_error_tendsto (omega E : ℕ → ℝ) (C R : ℝ)
    (hw : Tendsto omega atTop atTop) (hE : Tendsto E atTop atTop) :
    Tendsto (fun n => spectralNoTurnRealError C R (omega n) (E n)) atTop (𝓝 0) := by
  have he := spectralNoTurn_branch_error_tendsto omega E C R hw hE
  have hs : Tendsto (fun n => (Real.sqrt (omega n/2))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp (hw.atTop_div_const (by norm_num)))
  have hi := tendsto_inv_atTop_zero.comp hw
  have ht := (((he.const_mul 5).div_const (Real.exp (-256))).add
    (hs.const_mul ((2/R+4*C/R^3)/4))).const_mul 2
  convert ht.add (hi.const_mul 16) using 1
  · funext n
    dsimp only [spectralNoTurnRealError,Function.comp_def]
    ring
  · simp only [mul_zero,zero_div,add_zero]

theorem spectralNoTurn_outgoing_slope_limit
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ) (C R : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ |gamma n| ≤ 8 ∧ 0 < E n ∧
      (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n))
    (q : ℕ → ℝ → ℂ × ℂ)
    (hq : ∀ᶠ n in atTop, ContinuousOn (q n) (Icc R (E n)) ∧
      q n (E n) = spectralOscillatoryData (-1) (Real.sqrt (Real.sqrt
        (homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
      ∀ t ∈ Ioo R (E n), HasDerivAt (q n) (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+
          Complex.I*(gamma n : ℂ)) (q n t)) t) :
    (∀ᶠ n in atTop, (q n R).1 ≠ 0) ∧
      Tendsto (fun n => ((q n R).2/(q n R).1)/
        (Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) R) : ℂ)) atTop (𝓝 (-Complex.I)) := by
  obtain ⟨hE,hp⟩ := spectralNoTurn_eventual_data ell b omega gamma E C R hC hR hw hdata
  have hlim := spectralNoTurn_real_error_tendsto omega E C R hw hE
  have hb : ∀ᶠ n in atTop, (q n R).1 ≠ 0 ∧
      ‖((q n R).2/(q n R).1)/
        (Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) R) : ℂ)+Complex.I‖ ≤
        spectralNoTurnRealError C R (omega n) (E n) := by
    filter_upwards [hdata,hq,hp,hw.eventually (eventually_ge_atTop (16 : ℝ))]
      with n hn hqn hpn h16
    let eta := (ell n : ℝ)*(ell n+10)
    let F := homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) R
    let p := spectralLiouvilleMomentum 1 (-1) (b n) eta (omega n) (gamma n) R
    let K := 2/R+4*C/R^3
    have heta : 0 ≤ eta := by dsimp only [eta]; positivity
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hFlo : omega n/2 ≤ F := by
      have hh := spectralNoTurn_frequency_lower (b n) eta (omega n) C R R
        hn.1 hpn.1 hR le_rfl hn.2.2.2.1 hCR
      dsimp only [F]
      nlinarith [sq_nonneg R]
    have hF : 0 < F := (half_pos hpn.1).trans_le hFlo
    have hgF : |gamma n| ≤ F := hn.2.1.trans (by linarith)
    have hgE : |gamma n| ≤ homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) (E n) := by
      have hh := spectralNoTurn_frequency_lower (b n) eta (omega n) C R (E n)
        hn.1 hpn.1 hR hpn.2.2.1 hn.2.2.2.1 hCR
      nlinarith [hn.2.1,sq_nonneg (E n)]
    have hl := spectralNoTurn_outgoing_logarithmic_bound (b n) eta (omega n) (gamma n) C R (E n)
      hn.1 heta hpn.1 hC hpn.2.1 hR hpn.2.2.1 hn.2.2.1 hpn.2.2.2.1 hn.2.2.2.1 hCR
      hn.2.1 hpn.2.2.2.2.1 hpn.2.2.2.2.2.1 hgE hpn.2.2.2.2.2.2 (q n) hqn.1 hqn.2.1 hqn.2.2
    let eps := 5*spectralNoTurnBranchError C R (omega n) (E n)/Real.exp (-256)+K/(4*‖p‖)
    have heps : 0 ≤ eps := (norm_nonneg _).trans hl.2
    have hreal := spectralPositiveMomentum_ratio_error F (gamma n) eps
      ((q n R).2/(q n R).1) hF hgF heps (by
        simpa only [eps,K,p,F,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul] using hl.2)
    have hpnorm : Real.sqrt (omega n/2) ≤ ‖p‖ :=
      spectralNoTurn_momentum_lower (b n) eta (omega n) (gamma n) C R R
        hn.1 hpn.1 hR le_rfl hn.2.2.2.1 hCR
    have hc : K/(4*‖p‖) ≤ K/(4*Real.sqrt (omega n/2)) :=
      div_le_div_of_nonneg_left hK (by positivity) (by linarith)
    have hg : |gamma n|/F ≤ 16/omega n := by
      calc
        _ ≤ 8/(omega n/2) := div_le_div₀ (by norm_num) hn.2.1 (half_pos hpn.1) hFlo
        _ = _ := by ring
    refine ⟨hl.1,hreal.trans ?_⟩
    dsimp only [spectralNoTurnRealError,eps,K] at *
    linarith
  refine ⟨hb.mono (fun _ hn => hn.1),?_⟩
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [hb,hlim.eventually (gt_mem_nhds heps)] with n hn hsmall
  rw [dist_eq_norm,sub_neg_eq_add]
  exact hn.2.trans_lt hsmall

end DefocusingNLS

end OAI
