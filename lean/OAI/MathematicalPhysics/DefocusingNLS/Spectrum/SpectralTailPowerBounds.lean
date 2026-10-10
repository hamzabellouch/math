import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralParameterShearLogJets
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailEulerPhysical
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingEstimates

namespace OAI

/-! Bounds for every physical radial derivative from the normalized logarithmic jets. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "V" => ℂ × ℂ

noncomputable def spectralPowerValues (νp νm : ℂ) (f g : ℝ → ℂ) (r : ℝ) : V :=
  homogeneousPhysicalLogColumn νp νm f g (Real.log r)

theorem spectralPowerValues_smooth (νp νm : ℂ) (f g : ℝ → ℂ) (L : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Ioi L)) (hg : ContDiffOn ℝ ∞ g (Ioi L)) :
    ContDiffOn ℝ ∞ (spectralPowerValues νp νm f g) (Ioi (Real.exp L)) := by
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (Real.exp L)) :=
    Real.contDiffOn_log.mono (fun r hr => (lt_trans (Real.exp_pos L) hr).ne')
  have hmap : MapsTo Real.log (Ioi (Real.exp L)) (Ioi L) := by
    intro r hr
    simpa only [mem_Ioi,Real.log_exp] using
      Real.log_lt_log (Real.exp_pos L) hr
  have hfp := hf.comp hlog hmap
  have hgp := hg.comp hlog hmap
  have hEp : ContDiffOn ℝ ∞ (fun r : ℝ => Complex.exp (νp*(Real.log r : ℂ)))
      (Ioi (Real.exp L)) :=
    Complex.contDiff_exp.comp_contDiffOn
      (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hlog))
  have hEm : ContDiffOn ℝ ∞ (fun r : ℝ => Complex.exp (νm*(Real.log r : ℂ)))
      (Ioi (Real.exp L)) :=
    Complex.contDiff_exp.comp_contDiffOn
      (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hlog))
  exact (hEp.mul hfp).prodMk (hEm.mul hgp)

theorem spectralPowerValues_derivative_bound (νp νm : ℂ) (hsame : νp.re=νm.re)
    (f g : ℝ → ℂ) (σ : ℝ) (hf : HasLogJetBound σ f) (hg : HasLogJetBound σ g)
    (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ r in atTop,
      ‖iteratedDeriv n (spectralPowerValues νp νm f g) r‖ ≤
        C*r^(νp.re+σ-(n : ℝ)) := by
  obtain ⟨Lf,hfs⟩ := hf.smooth
  obtain ⟨Lg,hgs⟩ := hg.smooth
  let L := max Lf Lg
  have hfl := hfs.mono (Ioi_subset_Ioi (le_max_left Lf Lg))
  have hgl := hgs.mono (Ioi_subset_Ioi (le_max_right Lf Lg))
  have hU := spectralPowerValues_smooth νp νm f g L hfl hgl
  have hE := (homogeneousNormalizedEuler_bound_order νp f σ hf n).pair
    (homogeneousNormalizedEuler_bound_order νm g σ hg n)
  obtain ⟨C,hC,hbound⟩ := hE.bound 0
  refine ⟨C,hC,?_⟩
  have hlogbound := Real.tendsto_log_atTop.eventually hbound
  filter_upwards [hlogbound,eventually_gt_atTop (Real.exp L)] with r hr hrL
  have hr₀ : 0<r := (Real.exp_pos L).trans hrL
  have ht : L<Real.log r := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos L) hrL
  let t := Real.log r
  have hphys := homogeneousEulerDeriv_physical_tail (spectralPowerValues νp νm f g) L hU n t ht
  have heq : (fun s => spectralPowerValues νp νm f g (Real.exp s))=
      homogeneousPhysicalLogColumn νp νm f g := by
    funext s
    simp only [spectralPowerValues,Real.log_exp]
  rw [heq,homogeneousPhysicalLogColumn_euler νp νm f g L hfl hgl n t ht] at hphys
  have hnp : ‖Complex.exp (νp*(t : ℂ))‖=Real.exp (νp.re*t) := by
    simp only [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have hnm : ‖Complex.exp (νm*(t : ℂ))‖=Real.exp (νp.re*t) := by
    simpa only [hsame] using (show ‖Complex.exp (νm*(t : ℂ))‖=Real.exp (νm.re*t) by
      simp only [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero])
  have hn := congrArg norm hphys
  rw [homogeneousDiagonal_norm _ _ _ (Real.exp_pos _).le hnp hnm,norm_smul,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hn
  simp only [iteratedDeriv_zero] at hr
  have hr' : ‖homogeneousNormalizedEulerColumn νp νm f g n t‖≤C*Real.exp (σ*t) := hr
  have hprod : Real.exp ((n : ℝ)*t)*
      ‖iteratedDeriv n (spectralPowerValues νp νm f g) (Real.exp t)‖ ≤
      C*Real.exp ((νp.re+σ)*t) := by
    rw [← hn]
    calc
      _ ≤ Real.exp (νp.re*t)*(C*Real.exp (σ*t)) :=
        mul_le_mul_of_nonneg_left hr' (Real.exp_pos _).le
      _ = _ := by rw [add_mul,Real.exp_add]; ring
  have hout : ‖iteratedDeriv n (spectralPowerValues νp νm f g) (Real.exp t)‖ ≤
      C*Real.exp ((νp.re+σ-(n : ℝ))*t) := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos ((n : ℝ)*t))).mp
    calc
      _ ≤ C*Real.exp ((νp.re+σ)*t) := by simpa only [mul_comm] using hprod
      _ = _ := by
        calc
          C*Real.exp ((νp.re+σ)*t) =
              C*Real.exp ((n : ℝ)*t+(νp.re+σ-(n : ℝ))*t) := by congr 2; ring
          _ = _ := by rw [Real.exp_add]; ring
  simpa only [t,Real.exp_log hr₀,Real.rpow_def_of_pos hr₀,mul_comm] using hout

end DefocusingNLS

end OAI
