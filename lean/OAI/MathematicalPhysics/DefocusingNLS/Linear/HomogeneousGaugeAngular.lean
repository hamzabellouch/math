import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGaugeDecay
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularUpperExclusion
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLogGaugeCoefficients

namespace OAI

/-! # The real angular system of the actual complex gauge equation -/

open Set Filter Topology Asymptotics
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

noncomputable def homogeneousGaugeRealChannels (f g : ℝ → ℂ) : Fin 4 → ℝ → ℝ :=
  ![fun r => (f r).re, fun r => (f r).im, fun r => (g r).re, fun r => (g r).im]

theorem homogeneousCoordinate_derivatives (F : ℝ → ℂ) (hF : ContDiff ℝ 2 F)
    (L : ℂ →L[ℝ] ℝ) :
    deriv (fun r => L (F r)) = (fun r => L (deriv F r)) ∧
      deriv (deriv (fun r => L (F r))) = (fun r => L (deriv (deriv F) r)) := by
  have hd : deriv (fun r => L (F r)) = (fun r => L (deriv F r)) := by
    funext r
    exact (L.hasFDerivAt.comp_hasDerivAt r
      (hF.differentiable (by norm_num) r).hasDerivAt).deriv
  refine ⟨hd, ?_⟩
  rw [hd]
  funext r
  exact (L.hasFDerivAt.comp_hasDerivAt r
    ((hF.deriv' (n := 1)).differentiable (by norm_num) r).hasDerivAt).deriv

private theorem gauge_angular_action (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (eta : ℝ) (q f : ℝ → ℝ) (r : ℝ) (hr : 0 < r) :
    radialAngularScalarAction n z eta q f r = radialMassDensity n z r *
      (-deriv (deriv f) r - (11 / r + 2 * (deriv (radialMatchedProfile n z) r /
        radialMatchedProfile n z r).re) * deriv f r + (q r + eta / r ^ 2) * f r) := by
  have ha : radialAngularDensity n z r = radialMassDensity n z r / r ^ 2 := by
    unfold radialAngularDensity radialMassDensity
    field_simp [hr.ne']
  rw [radialAngularScalarAction, radialScalarAction,
    radialMassLaplacian_logarithmic n z hX f r hr, ha]
  ring

private theorem gauge_coefficients_real (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (r : ℝ) (hr : 0 < r) :
    let Q := radialMatchedEvenProfile n z
    (11 / (r : ℂ) + deriv Q r / Q r + star (deriv Q r) / star (Q r) =
      ((11 / r + 2 * (deriv (radialMatchedProfile n z) r / radialMatchedProfile n z r).re : ℝ) : ℂ)) ∧
    ((r : ℂ) / 2 - Complex.I * (deriv Q r / Q r - star (deriv Q r) / star (Q r)) =
      (radialMatchedVelocity n z r : ℂ)) ∧
    (2 * ((n + radialInnerShootingThreshold : ℕ) : ℂ) *
      ((‖Q r‖ ^ (2 * (n + radialInnerShootingThreshold)) : ℝ) : ℂ) =
      (radialSpectralPressure n z r : ℂ)) := by
  intro Q
  have he := radialMatchedEvenProfile_eventuallyEq n z r hr
  have hmass (q dq : ℂ) : dq / q + star dq / star q = ((2 * (dq / q).re : ℝ) : ℂ) := by
    rw [← star_div₀]
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    · ring
    · ring
  have hpress : 2 * ((n + radialInnerShootingThreshold : ℕ) : ℝ) *
      ‖Q r‖ ^ (2 * (n + radialInnerShootingThreshold)) = radialSpectralPressure n z r := by
    have ha := radialShootingA_power n (profileMatchingParameter z)
    have han := (radialShootingA_bounds n (profileMatchingParameter z)).1.ne'
    dsimp only [radialSpectralPressure]
    rw [show Q r = radialMatchedProfile n z r from he.eq_of_nhds]
    apply (eq_div_iff han).2
    calc
      _ = (2 * radialShootingA n * ((n + radialInnerShootingThreshold : ℕ) : ℝ)) *
          ‖radialMatchedProfile n z r‖ ^ (2 * (n + radialInnerShootingThreshold)) := by ring
      _ = _ := by rw [ha, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [Q]
    rw [add_assoc, hmass, he.eq_of_nhds, he.deriv_eq]
    push_cast; rfl
  · dsimp only [Q]
    rw [spectralLogGauge_transport, he.eq_of_nhds, he.deriv_eq,
      radialMatchedVelocity_formula n z hX hz r hr]
    rfl
  · exact_mod_cast hpress

theorem homogeneousGauge_angular_system (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (eta : ℝ) (lam : ℂ)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeEigenpair (n + radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) (eta : ℂ) lam f g) :
    HasAngularSpectralSystem n z eta lam.re lam.im (homogeneousGaugeRealChannels f g) := by
  obtain ⟨hfr, hfrr⟩ := homogeneousCoordinate_derivatives f hf Complex.reCLM
  obtain ⟨hfi, hfii⟩ := homogeneousCoordinate_derivatives f hf Complex.imCLM
  obtain ⟨hgr, hgrr⟩ := homogeneousCoordinate_derivatives g hg Complex.reCLM
  obtain ⟨hgi, hgii⟩ := homogeneousCoordinate_derivatives g hg Complex.imCLM
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hfr hfrr hfi hfii hgr hgrr hgi hgii
  intro r hr
  rcases hr.eq_or_lt with hr | hr
  · subst r
    simp [homogeneousGaugeRealChannels, radialAngularScalarAction, radialScalarAction,
      radialMassLaplacian, radialMassDensity, radialMassSlope, radialAngularDensity]
  obtain ⟨hB, hW, hP⟩ := gauge_coefficients_real n z hX hz r hr
  obtain ⟨h1, h2⟩ := he r hr
  rw [hB, hW] at h1 h2
  rw [hP] at h2
  have heta : (eta : ℂ) / (r : ℂ) ^ 2 = ((eta / r ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [heta] at h1 h2
  have h1r := congrArg Complex.re h1
  have h1i := congrArg Complex.im h1
  have h2r := congrArg Complex.re h2
  have h2i := congrArg Complex.im h2
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at h1r h1i h2r h2i
  dsimp only [homogeneousGaugeRealChannels, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] at *
  simp only [gauge_angular_action n z hX eta _ _ r hr, radialSpectralTest,
    hfrr, hfii, hgrr, hgii]
  simp only [hfr, hfi, hgr, hgi]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination radialMassDensity n z r * h2r
  · linear_combination radialMassDensity n z r * h2i
  · linear_combination -radialMassDensity n z r * h1r
  · linear_combination -radialMassDensity n z r * h1i

end DefocusingNLS

end OAI
