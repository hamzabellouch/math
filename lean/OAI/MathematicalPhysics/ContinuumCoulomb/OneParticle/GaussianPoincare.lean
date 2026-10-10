import OAI.Analysis.KLS.Spectral.RegularPoincare
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace OAI

/-! One-dimensional Gaussian Poincare inequality derived from the
Brascamp–Lieb theorem. This is the spectral input needed for the
transverse oscillator; no spectral assertion is assumed here. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace ContinuumCoulomb
open LeanBlast.KLS

private def gaussianPotential (freq : ℝ) (x : Space 1) : ℝ := freq*‖x‖^2

private theorem gaussianPotential_derivative (freq : ℝ) :
    fderiv ℝ (gaussianPotential freq) =
      ⇑((2*freq) • (innerSL ℝ (E := Space 1))) := by
  funext x
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul freq).fderiv
  change fderiv ℝ (fun y : Space 1 => freq*‖y‖^2) x = _
  rw [h]
  ext v
  simp only [smul_apply,two_smul,add_apply,smul_eq_mul]
  ring

private theorem gaussianPotential_hessian (freq : ℝ) (x v : Space 1) :
    fderiv ℝ (fderiv ℝ (gaussianPotential freq)) x v v = (2*freq)*‖v‖^2 := by
  rw [gaussianPotential_derivative]
  rw [(((2*freq) • (innerSL ℝ (E := Space 1))).hasFDerivAt (x := x)).fderiv]
  change (2*freq)*inner ℝ v v = (2*freq)*‖v‖^2
  rw [real_inner_self_eq_norm_sq]

private theorem gaussianPotential_regular {freq : ℝ} (hf : 0 < freq) :
    IsRegularPotential (gaussianPotential freq) (2*freq) (2*freq) where
  contDiff := contDiff_const.mul (contDiff_norm_sq ℝ)
  lower_pos := by positivity
  le_upper := le_rfl
  lower_bound x v := (gaussianPotential_hessian freq x v).ge
  upper_bound x v := (gaussianPotential_hessian freq x v).le

private theorem gaussianPotential_integrable {freq : ℝ} (hf : 0 < freq) :
    Integrable (fun x => Real.exp (-gaussianPotential freq x)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Space 1) (b := (freq:ℂ)) (by simpa using hf) 0 0
  have hc : Integrable (fun x : Space 1 => Complex.exp ((-freq*‖x‖^2:ℝ):ℂ)) := by
    simpa only [zero_mul,add_zero,Complex.ofReal_mul,Complex.ofReal_neg,
      Complex.ofReal_pow] using h
  simpa only [Complex.norm_exp,Complex.ofReal_re,gaussianPotential,neg_mul] using hc.norm

theorem gaussian_weight_integrable {freq : ℝ} (hf : 0 < freq) :
    Integrable (fun x : Space 1 => Real.exp (-(freq*‖x‖^2))) :=
  gaussianPotential_integrable hf

/-- Gaussian variance is bounded by its Dirichlet form with the exact
oscillator gap constant. -/
theorem gaussian_poincare_test {freq : ℝ} (hf : 0 < freq)
    (f : Space 1 → ℝ) (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (2*freq)*variance (potentialMeasure (fun x : Space 1 => freq*‖x‖^2)) f ≤
      dirichletEnergy (potentialMeasure (fun x : Space 1 => freq*‖x‖^2)) f :=
  (gaussianPotential_regular hf).poincare (gaussianPotential_integrable hf) ⟨hs,hc⟩

end ContinuumCoulomb

end

end OAI
