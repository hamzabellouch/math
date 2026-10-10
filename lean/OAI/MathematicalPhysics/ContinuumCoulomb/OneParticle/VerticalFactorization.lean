import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalCappedForm

namespace OAI

/-! The oscillator ground-state transform on compact C¹ functions, with all
boundary terms discharged by compact support. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem vertical_cross_integrable (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) : Integrable (fun z => 2*z*u z*deriv u z) := by
  have hd := hu.continuous_deriv (by norm_num)
  exact (((continuous_const.mul continuous_id).mul hu.continuous).mul hd).integrable_of_hasCompactSupport
    hc.deriv.mul_left

theorem vertical_cross_identity (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    (∫ z : ℝ, 2*z*u z*deriv u z) = -(∫ z : ℝ, u z^2) := by
  have hd (z : ℝ) : deriv (fun x => u x^2) z = 2*u z*deriv u z := by
    have h := (hu.differentiable (by norm_num) z).hasDerivAt
    have hh := h.fun_mul h
    have he : (fun x => u x*u x) = (fun x => u x^2) := by funext x; ring
    rw [he] at hh
    rw [hh.deriv]
    ring
  have hc2 : HasCompactSupport (fun z => u z^2) :=
    hc.comp_left (g := fun x : ℝ => x^2) (by norm_num)
  have hA : Integrable (fun z => fderiv ℝ (fun x => u x^2) z 1*z) := by
    have he : (fun z => fderiv ℝ (fun x => u x^2) z 1*z) =
        (fun z => 2*z*u z*deriv u z) := by
      funext z
      rw [fderiv_apply_one_eq_deriv,hd]
      ring
    rw [he]
    exact vertical_cross_integrable u hu hc
  have hB : Integrable (fun z => u z^2*fderiv ℝ (fun x : ℝ => x) z 1) := by
    have hcont : Continuous (fun z => u z^2) := by fun_prop
    have hi : Integrable (fun z => u z^2) := hcont.integrable_of_hasCompactSupport hc2
    simpa only [fderiv_apply_one_eq_deriv,deriv_id'',mul_one] using hi
  have hfg : Integrable (fun z => u z^2*z) :=
    ((hu.continuous.pow 2).mul continuous_id).integrable_of_hasCompactSupport hc2.mul_right
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hA hB hfg
    (fun z _ => ((hu.pow 2).differentiable (by norm_num) z))
    (fun z _ => differentiableAt_id)
  simp only [fderiv_apply_one_eq_deriv,deriv_id'',mul_one,hd] at h
  have he : (∫ z : ℝ, 2*u z*deriv u z*z) = ∫ z : ℝ, 2*z*u z*deriv u z := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by ring
  rw [he] at h
  linarith

theorem vertical_factorized_energy (freq : ℝ) (u : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (1/2:ℝ)*(∫ z : ℝ, (deriv u z+freq*z*u z)^2) =
      verticalForm freq u - (freq/2)*(∫ z : ℝ, u z^2) := by
  have hiD := vertical_deriv_square_integrable u hu hc
  have hiP := vertical_product_integrable (fun z => z^2) u
    (continuous_id.pow 2) hu.continuous hc
  have hiC := vertical_cross_integrable u hu hc
  have he : (fun z => (deriv u z+freq*z*u z)^2) =
      (fun z => (deriv u z)^2+freq^2*(z^2*u z^2)+freq*(2*z*u z*deriv u z)) := by
    funext z
    ring
  rw [he,integral_add (f := fun z => (deriv u z)^2+freq^2*(z^2*u z^2))
    (g := fun z => freq*(2*z*u z*deriv u z)) (hiD.add (hiP.const_mul _)) (hiC.const_mul _),
    integral_add (f := fun z => (deriv u z)^2) (g := fun z => freq^2*(z^2*u z^2))
      hiD (hiP.const_mul _),integral_const_mul,integral_const_mul,
    vertical_cross_identity u hu hc]
  unfold verticalForm
  ring

end ContinuumCoulomb

end

end OAI
