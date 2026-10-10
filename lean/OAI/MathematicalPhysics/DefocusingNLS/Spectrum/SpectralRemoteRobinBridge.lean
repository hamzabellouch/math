import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationRemote
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationGeometry

namespace OAI

/-! Undoing the remote eigenvector frame gives the exact scalar Robin phase,
including the radial Liouville factor and the centrifugal correction. -/

namespace DefocusingNLS

theorem spectralRemote_robin_phase_bound (h c F E : ℝ) (hh : h^2 = 1)
    (hE : 0 < E) (hc : |c| ≤ 1/32) (hF : 0 ≤ F)
    (hFG : |F-E^2*(1/16-c)| ≤ 2) :
    ‖(E : ℂ)*homogeneousSpectralLocalizationRemoteRoot h 1 c+
      homogeneousSpectralLocalizationSlope h E-(h : ℂ)*Complex.I*(Real.sqrt F : ℂ)‖ ≤ 22/E := by
  let s := Real.sqrt (1/16-c)
  let f := Real.sqrt F
  have hc' := (abs_le.mp hc).2
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hf0 : 0 ≤ f := Real.sqrt_nonneg _
  have hs2 : s^2 = 1/16-c := Real.sq_sqrt (by linarith)
  have hf2 : f^2 = F := Real.sq_sqrt hF
  have hs : 1/8 ≤ s := by nlinarith
  have hprod : |f-E*s| *(f+E*s) ≤ 2 := by
    have he : (f-E*s)*(f+E*s) = F-E^2*(1/16-c) := by nlinarith [hs2,hf2]
    have hh' := hFG
    rw [← he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ f+E*s)] at hh'
    exact hh'
  have hd : |f-E*s| ≤ 16/E := by
    apply (le_div_iff₀ hE).mpr
    nlinarith [abs_nonneg (f-E*s),mul_le_mul_of_nonneg_left hs hE.le]
  have habs : |h| = 1 := by nlinarith [sq_abs h,abs_nonneg h]
  have heq : (E : ℂ)*homogeneousSpectralLocalizationRemoteRoot h 1 c+
      homogeneousSpectralLocalizationSlope h E-(h : ℂ)*Complex.I*(Real.sqrt F : ℂ) =
      (11/(2*E) : ℝ)+(h : ℂ)*Complex.I*((E*s-f : ℝ) : ℂ) := by
    dsimp only [homogeneousSpectralLocalizationRemoteRoot,homogeneousSpectralLocalizationSlope,s,f]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖((11/(2*E) : ℝ) : ℂ)‖+‖(h : ℂ)*Complex.I*((E*s-f : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = 11/(2*E)+|E*s-f| := by
      rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Complex.norm_real,
        Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,Complex.norm_I,habs,
        abs_of_nonneg (by positivity : 0 ≤ 11/(2*E))]
      ring
    _ ≤ 11/(2*E)+16/E := add_le_add le_rfl (by simpa only [abs_sub_comm] using hd)
    _ ≤ 22/E := by
      apply (le_div_iff₀ hE).mpr
      field_simp
      norm_num

theorem spectralRemote_actual_robin_phase_bound (h b eta omega E : ℝ) (hh : h^2 = 1)
    (hE : 8 ≤ E) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hc : |h*omega/E^2+eta/E^4| ≤ 1/32) :
    ‖(E : ℂ)*homogeneousSpectralLocalizationRemoteRoot h 1 (h*omega/E^2+eta/E^4)+
      homogeneousSpectralLocalizationSlope h E-(h : ℂ)*Complex.I*
        (Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega E) : ℂ)‖ ≤ 22/E := by
  have hEp : 0 < E := by linarith
  let c := h*omega/E^2+eta/E^4
  let F := homogeneousSpectralLocalizationFrequency h b eta omega E
  have he : F-E^2*(1/16-c) = b-99/(4*E^2) := by
    dsimp only [F,c,homogeneousSpectralLocalizationFrequency]
    field_simp
    ring
  have hsmall : 99/(4*E^2) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have hdiff : |F-E^2*(1/16-c)| ≤ 2 := by
    rw [he]
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg hb,abs_of_nonneg (by positivity : 0 ≤ 99/(4*E^2))]
      linarith)
  have hFlo : 0 ≤ F := by
    have hcu : c ≤ 1/32 := (abs_le.mp hc).2
    have hG : E^2/32 ≤ E^2*(1/16-c) := by nlinarith [sq_nonneg E]
    have hdl := (abs_le.mp hdiff).1
    nlinarith
  exact spectralRemote_robin_phase_bound h c F E hh hEp hc hFlo hdiff

end DefocusingNLS

end OAI
