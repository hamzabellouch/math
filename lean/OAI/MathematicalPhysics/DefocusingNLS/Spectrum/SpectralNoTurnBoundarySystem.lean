import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnGreen
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNormalizedBoundarySystem
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRegularizedWeight

namespace OAI

/-! The no-turn comparison supplies the exact outgoing boundary system
and a uniform bound for extension of the inner boundary value. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralNoTurn_boundary_systems
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ) (C R : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ |gamma n| ≤ 8 ∧ 0 < E n ∧
      (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    ∃ K J : ℝ, 0 ≤ K ∧ 0 ≤ J ∧ ∀ᶠ n in atTop,
      ∃ S : SpectralScalarBoundarySystem R (E n) K,
        S.k = (fun r => Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) (gamma n) r‖) ∧
        S.V = (fun r => (homogeneousSpectralLocalizationFrequency (-1) (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) r : ℂ)+Complex.I*(gamma n : ℂ)) ∧
        S.beta = -Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1)
          (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (E n)) : ℂ) ∧
        S.U (E n) = spectralOscillatoryData (-1) (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency (-1) (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
        ∀ z : ℂ, ∀ r ∈ Icc R (E n),
          spectralShellNorm (S.k r) (S.extension z r) ≤ J*S.k R*‖z‖ := by
  obtain ⟨K,J,hK,hJ,hall⟩ := spectralNoTurn_outgoing_green_extension_uniform
    ell b omega gamma E C R hC hR hCR hw hdata
  refine ⟨K,J,hK,hJ,?_⟩
  filter_upwards [hall,hdata,hw.eventually (eventually_gt_atTop 0),
    hw.eventually (eventually_ge_atTop (R^2))] with n hn hdn hwp hlarge
  obtain ⟨U,D,W,hUc,hUE,hUD,hUR,hDc,hDR,hDD,hW,hdet,hgreen,hext⟩ := hn
  obtain ⟨hb,hg,hEp,hL,hscale⟩ := hdn
  have hRE : R ≤ E n := by
    have hm := hlarge.trans (le_max_right ((ell n : ℝ)+1) (omega n))
    nlinarith [sq_nonneg R]
  let eta := (ell n : ℝ)*(ell n+10)
  let k := fun r => Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) (b n) eta (omega n) (gamma n) r‖
  let V := fun r => (homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) r : ℂ)+
    Complex.I*(gamma n : ℂ)
  have hV : ContinuousOn V (Icc R (E n)) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun r hr =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt (-1) (b n) eta (omega n) r
        (hR.trans_le hr.1)).continuousAt.continuousWithinAt)).add continuousOn_const
  have hk : ContinuousOn k (Icc R (E n)) := by
    simpa only [k,V,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,
      one_mul,spectralComplexSqrt_norm,Function.comp_def] using
      Real.continuous_sqrt.comp_continuousOn (Real.continuous_sqrt.comp_continuousOn hV.norm)
  have hkp : ∀ r ∈ Icc R (E n), 0 < k r := by
    intro r hr
    have hf : 0 < homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) r :=
      lt_of_lt_of_le (by positivity) (spectralNoTurn_frequency_lower (b n) eta (omega n) C R r
        hb hwp hR hr.1 hL hCR)
    exact spectralLiouville_norm_weight_pos 1 (-1) (b n) eta (omega n) (gamma n) r
      (by norm_num) hf.ne'
  let S := spectralNormalizedBoundarySystem R (E n) K (-1)
    (homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) (E n)) hRE
    k V D U W hk hkp hDc.continuousOn hUc.continuousOn hDD hUD hDR hUE hW hdet hgreen
  refine ⟨S,rfl,rfl,?_,hUE,hext⟩
  simp only [S,spectralNormalizedBoundarySystem,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,eta]

end DefocusingNLS

end OAI
