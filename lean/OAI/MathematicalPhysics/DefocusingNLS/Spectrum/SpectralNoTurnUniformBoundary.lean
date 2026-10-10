import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnUniformGreen
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNormalizedBoundarySystem
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRegularizedWeight

namespace OAI

/-! The no-turn comparison supplies the exact outgoing boundary system
and a uniform bound for extension of the inner boundary value. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralNoTurn_uniform_boundary_systems
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ) (C R B : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hRB : R ≤ B) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ |gamma n| ≤ 8 ∧ 0 < E n ∧
      (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    ∃ K J : ℝ, 0 ≤ K ∧ 0 ≤ J ∧ ∀ᶠ n in atTop, ∀ L ∈ Icc R B,
      ∃ S : SpectralScalarBoundarySystem L (E n) K,
        S.k = (fun r => Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) (gamma n) r‖) ∧
        S.V = (fun r => (homogeneousSpectralLocalizationFrequency (-1) (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) r : ℂ)+Complex.I*(gamma n : ℂ)) ∧
        S.beta = -Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1)
          (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (E n)) : ℂ) ∧
        S.U (E n) = spectralOscillatoryData (-1) (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency (-1) (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
        ∀ z : ℂ, ∀ r ∈ Icc L (E n),
          spectralShellNorm (S.k r) (S.extension z r) ≤ J*S.k L*‖z‖ := by
  obtain ⟨K,J,hK,hJ,hall⟩ := spectralNoTurn_outgoing_green_extension_uniform_inner
    ell b omega gamma E C R B hC hR hRB hCR hw hdata
  refine ⟨K,J,hK,hJ,?_⟩
  filter_upwards [hall,hdata,hw.eventually (eventually_gt_atTop 0),
    hw.eventually (eventually_ge_atTop (B^2))] with n hn hdn hwp hlarge
  intro L hL
  have hL0 : 0 < L := hR.trans_le hL.1
  have hCL : 2*C ≤ L^2 := hCR.trans (pow_le_pow_left₀ hR.le hL.1 2)
  obtain ⟨U,D,W,hUc,hUE,hUD,hUR,hDc,hDR,hDD,hW,hdet,hgreen,hext⟩ := hn L hL
  obtain ⟨hb,hg,hEp,hAngular,hscale⟩ := hdn
  have hRE : L ≤ E n := by
    have hm := hlarge.trans (le_max_right ((ell n : ℝ)+1) (omega n))
    nlinarith [sq_nonneg B,hL.2]
  let eta := (ell n : ℝ)*(ell n+10)
  let k := fun r => Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) (b n) eta (omega n) (gamma n) r‖
  let V := fun r => (homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) r : ℂ)+
    Complex.I*(gamma n : ℂ)
  have hV : ContinuousOn V (Icc L (E n)) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun r hr =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt (-1) (b n) eta (omega n) r
        (hL0.trans_le hr.1)).continuousAt.continuousWithinAt)).add continuousOn_const
  have hk : ContinuousOn k (Icc L (E n)) := by
    simpa only [k,V,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,
      one_mul,spectralComplexSqrt_norm,Function.comp_def] using
      Real.continuous_sqrt.comp_continuousOn (Real.continuous_sqrt.comp_continuousOn hV.norm)
  have hkp : ∀ r ∈ Icc L (E n), 0 < k r := by
    intro r hr
    have hf : 0 < homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) r :=
      lt_of_lt_of_le (by positivity) (spectralNoTurn_frequency_lower (b n) eta (omega n) C L r
        hb hwp hL0 hr.1 hAngular hCL)
    exact spectralLiouville_norm_weight_pos 1 (-1) (b n) eta (omega n) (gamma n) r
      (by norm_num) hf.ne'
  let S := spectralNormalizedBoundarySystem L (E n) K (-1)
    (homogeneousSpectralLocalizationFrequency (-1) (b n) eta (omega n) (E n)) hRE
    k V D U W hk hkp hDc.continuousOn hUc.continuousOn hDD hUD hDR hUE hW hdet hgreen
  refine ⟨S,rfl,rfl,?_,hUE,hext⟩
  simp only [S,spectralNormalizedBoundarySystem,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,eta]

end DefocusingNLS

end OAI
