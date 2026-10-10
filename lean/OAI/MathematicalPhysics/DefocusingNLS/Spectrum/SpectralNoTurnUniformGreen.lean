import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnUniformTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnRadiusOrder
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnValue
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnEventual
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingComparison
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDirichletGreenScaled
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingExtensionBound

namespace OAI

/-! Construct the normalized outgoing comparison and its uniformly bounded
Dirichlet Green kernel in the no-turn channel. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralNoTurn_outgoing_green_extension_uniform_inner
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ) (C R B : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hRB : R ≤ B) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ |gamma n| ≤ 8 ∧ 0 < E n ∧
      (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    ∃ K J : ℝ, 0 ≤ K ∧ 0 ≤ J ∧ ∀ᶠ n in atTop, ∀ L ∈ Icc R B,
      let k := fun t => Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (gamma n) t‖
      ∃ (U D : ℝ → ℂ × ℂ) (W : ℂ), Continuous U ∧
        U (E n) = spectralOscillatoryData (-1) (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
        (∀ t ∈ Icc L (E n), HasDerivAt U (spectralScalarField
          ((homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+
            Complex.I*(gamma n : ℂ)) (U t)) t) ∧ (U L).1 ≠ 0 ∧
        Continuous D ∧ D L = (0,(k L : ℂ)) ∧
        (∀ t ∈ Icc L (E n), HasDerivAt D (spectralScalarField
          ((homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+
            Complex.I*(gamma n : ℂ)) (D t)) t) ∧
        W ≠ 0 ∧ (∀ t ∈ Icc L (E n), spectralScalarWronskian (D t) (U t) = W) ∧
        (∀ r ∈ Icc L (E n), ∀ t ∈ Icc L (E n),
          spectralShellNorm (k r) (spectralScalarGreenState D U W r t) ≤ K/(k t)) ∧
        ∀ z : ℂ, ∀ r ∈ Icc L (E n),
          spectralShellNorm (k r) ((z/(U L).1) • U r) ≤ J*k L*‖z‖ := by
  let Q : ℝ := 25*Real.exp (256+25/4)
  let c : ℝ := Real.exp (-256)/2
  let K : ℝ := Q*(3*Q)/c
  let J : ℝ := (3*Q)/c
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hp0 := spectralNoTurn_eventual_data ell b omega gamma E C R hC hR hw hdata
  have hp := hp0.2
  have ht := spectralNoTurn_uniform_inner_transfer ell b omega gamma E C R B hC hR hRB hCR hw hdata
  refine ⟨K,J,by dsimp only [K]; positivity,by dsimp only [J]; positivity,?_⟩
  filter_upwards [hdata,hp,ht,hw.eventually (eventually_ge_atTop (16 : ℝ)),
    hp0.1.eventually (eventually_ge_atTop B)] with n hn hpn htn h16 hBE
  intro L hL
  have hL0 : 0 < L := hR.trans_le hL.1
  have hLE : L ≤ E n := hL.2.trans hBE
  have hCL : 2*C ≤ L^2 := hCR.trans (pow_le_pow_left₀ hR.le hL.1 2)
  have hKL := (spectralNoTurn_derivative_radius_mono C R L hC hR hL.1).trans hpn.2.2.2.2.2.1
  have herrL := (spectralNoTurn_branch_radius_mono C R L (omega n) (E n) hC hR hL.1).trans hpn.2.2.2.2.2.2
  let eta := (ell n : ℝ)*(ell n+10)
  let p := spectralLiouvilleMomentum 1 (-1) (b n) eta (omega n) (gamma n)
  let k := fun t => Real.sqrt ‖p t‖
  let V := fun t => (homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) t : ℂ)+
    Complex.I*(gamma n : ℂ)
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  have hF (t : ℝ) (htr : R ≤ t) :
      0 < homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) t :=
    lt_of_lt_of_le (by positivity) (spectralNoTurn_frequency_lower (b n) eta (omega n) C R t
      hn.1 hpn.1 hR htr hn.2.2.2.1 hCR)
  have hgF : |gamma n| ≤ homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) (E n) := by
    have hf := spectralNoTurn_frequency_lower (b n) eta (omega n) C R (E n)
      hn.1 hpn.1 hR hpn.2.2.1 hn.2.2.2.1 hCR
    nlinarith [hn.2.1,sq_nonneg (E n)]
  obtain ⟨U,hUc,hUE,hflux,hUN,hUDR⟩ := spectralLiouville_outgoing_exists (-1) (b n) eta (omega n)
    (gamma n) R (E n) (by norm_num) hR hpn.2.2.1 (hF (E n) hpn.2.2.1) hgF
  have hUD (t : ℝ) (ht : t ∈ Icc L (E n)) : HasDerivAt U
      (spectralScalarField (V t) (U t)) t := hUDR t ⟨hL.1.trans ht.1,ht.2⟩
  obtain ⟨hval,hUR,_⟩ := spectralNoTurn_outgoing_value (b n) eta (omega n) (gamma n) C L (E n)
    hn.1 heta hpn.1 hC hpn.2.1 hL0 hLE hn.2.2.1 hpn.2.2.2.1 hn.2.2.2.1 hCL
    hn.2.1 hpn.2.2.2.2.1 hKL hgF herrL U hUc.continuousOn hUE
    (fun t htr => hUD t ⟨htr.1.le,htr.2.le⟩)
  have hk (t : ℝ) (htr : t ∈ Icc L (E n)) : 0 < k t :=
    spectralLiouville_norm_weight_pos 1 (-1) (b n) eta (omega n) (gamma n) t
      (by norm_num) (hF t (hL.1.trans htr.1)).ne'
  have hV : ContinuousOn V (Icc L (E n)) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun t htr =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt (-1) (b n) eta (omega n) t
        (hL0.trans_le htr.1)).continuousAt.continuousWithinAt)).add continuousOn_const
  have hUb (r : ℝ) (hr : r ∈ Icc L (E n)) : spectralShellNorm (k r) (U r) ≤ (3*Q)*1*Real.exp (0 : ℝ) := by
    have hh := (htn L hL U hUc.continuousOn (fun t htr => hUD t ⟨htr.1.le,htr.2.le⟩)
      r hr (E n) ⟨hLE,le_rfl⟩ hr.2).2
    have hb := hh.trans (mul_le_mul_of_nonneg_left hUN hQ)
    change spectralShellNorm (k r) (U r) ≤ Q*3 at hb
    simpa only [mul_one,Real.exp_zero,mul_comm Q] using hb
  obtain ⟨D,W,hDc,hDR,hDD,hW,hdet,_hDb,_hWb,hgreen⟩ :=
    spectralScalar_dirichlet_green_scaled_data L (E n) Q (3*Q) c 1 hLE hQ
      (by positivity) hc (by norm_num) V k (fun _ => 0) hV hk
      (by intro r hr s hs hrs; exact le_rfl) U hUc.continuousOn
      (fun t htr => hUD t ⟨htr.1.le,htr.2.le⟩) hUb
      (by simpa only [mul_one,Real.exp_zero] using hval)
      (by
        intro v hvc hvD r hr
        have hh := (htn L hL v hvc hvD L ⟨le_rfl,hLE⟩ r hr hr.1).1
        simpa only [sub_self,Real.exp_zero,mul_one] using hh)
  refine ⟨U,D,W,hUc,hUE,hUD,hUR,hDc,hDR,hDD,hW,hdet,?_,?_⟩
  · intro r hr t htr
    apply (hgreen r hr t htr).trans_eq
    dsimp only [K]
    ring
  · intro z r hr
    exact spectralOutgoing_extension_bound (k r) (k L) (3*Q) c 1 0 0 (U r) (U L) z
      (by positivity) hc (by norm_num) le_rfl (hUb r hr)
      (by simpa only [mul_one,Real.exp_zero] using hval)

end DefocusingNLS

end OAI
