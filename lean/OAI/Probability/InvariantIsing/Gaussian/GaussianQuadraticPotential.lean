import OAI.Analysis.KLS.Spectral.RegularPoincare
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace OAI

/-! The finite-dimensional quadratic potential for Gaussian Poincare. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace InvariantIsing

def gaussianQuadraticPotential {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1/2 : ℝ)*‖x‖^2

lemma gaussianQuadraticPotential_derivative (d : ℕ) :
    fderiv ℝ (gaussianQuadraticPotential (d := d))=
      ⇑(innerSL ℝ (E := EuclideanSpace ℝ (Fin d))) := by
  funext x
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1/2 : ℝ)).fderiv
  change fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => (1/2 : ℝ)*‖y‖^2) x = _
  rw [h]
  ext v
  simp only [smul_apply,two_smul,add_apply,smul_eq_mul]
  ring

lemma gaussianQuadraticPotential_hessian {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fderiv ℝ (gaussianQuadraticPotential (d := d))) x v v=‖v‖^2 := by
  rw [gaussianQuadraticPotential_derivative]
  rw [((innerSL ℝ (E := EuclideanSpace ℝ (Fin d))).hasFDerivAt (x := x)).fderiv]
  exact real_inner_self_eq_norm_sq v

lemma gaussianQuadraticPotential_regular (d : ℕ) :
    LeanBlast.KLS.IsRegularPotential (gaussianQuadraticPotential (d := d)) 1 1 where
  contDiff := contDiff_const.mul (contDiff_norm_sq ℝ)
  lower_pos := zero_lt_one
  le_upper := le_rfl
  lower_bound x v := by rw [gaussianQuadraticPotential_hessian,one_mul]
  upper_bound x v := by rw [gaussianQuadraticPotential_hessian,one_mul]

lemma gaussianQuadraticPotential_integrable (d : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-gaussianQuadraticPotential x)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin d)) (b := (1/2 : ℂ)) (by norm_num) 0 0
  have hc : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Complex.exp ((-(1/2 : ℝ)*‖x‖^2 : ℝ) : ℂ)) := by
    simpa only [zero_mul,add_zero,Complex.ofReal_mul,Complex.ofReal_neg,
      Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using h
  simpa only [Complex.norm_exp,Complex.ofReal_re,gaussianQuadraticPotential,neg_mul] using hc.norm

lemma gaussianQuadraticPotential_poincare_test {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : LeanBlast.KLS.IsTestFunction f) :
    LeanBlast.KLS.variance (LeanBlast.KLS.potentialMeasure gaussianQuadraticPotential) f ≤
      LeanBlast.KLS.dirichletEnergy (LeanBlast.KLS.potentialMeasure gaussianQuadraticPotential) f := by
  simpa only [one_mul] using (gaussianQuadraticPotential_regular d).poincare
    (gaussianQuadraticPotential_integrable d) hf

end InvariantIsing

end

end OAI
