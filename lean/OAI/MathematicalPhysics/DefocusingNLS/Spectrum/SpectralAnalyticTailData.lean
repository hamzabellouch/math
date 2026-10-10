import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNormalizedResidual
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoefficientForcing

namespace OAI

/-! The entire bounded forcing family for the actual-profile slow-column construction. -/

open Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def spectralAnalyticTailData (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) (A B : ℝ →ᵇ ℂ) (lam : ℂ) : CircularTailSpace :=
  let U := spectralOutgoingPolynomial (νp-2*lam) (νm-2*lam) η m P c j
  circularCoefficientForcing A B (boundedRadialPolynomial U.1) (boundedRadialPolynomial U.2)+
    spectralNormalizedResidual (νp-2*lam) (νm-2*lam) η m P c j

theorem spectralAnalyticTailData_analyticAt (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) (A B : ℝ →ᵇ ℂ) (z : ℂ) :
    AnalyticAt ℂ (spectralAnalyticTailData νp νm η m P c j A B) z := by
  have hp : AnalyticAt ℂ (fun lam : ℂ => νp-2*lam) z :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have hm : AnalyticAt ℂ (fun lam : ℂ => νm-2*lam) z :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have hc (k : ℕ) := spectralOutgoingPolynomial_coeff_analytic
    (fun lam => νp-2*lam) (fun lam => νm-2*lam) η m P c z hp hm j k
  have hd (lam : ℂ) := spectralOutgoingPolynomial_degree (νp-2*lam) (νm-2*lam) η m P c j
  exact (circularCoefficientForcing_analyticAt A B _ _ z
    (boundedRadialPolynomial_analyticAt _ j z (fun lam => (hd lam).1) (fun k => (hc k).1))
    (boundedRadialPolynomial_analyticAt _ j z (fun lam => (hd lam).2) (fun k => (hc k).2))).add
      (spectralNormalizedResidual_analyticAt _ _ η m P c j z hp hm)

theorem spectralAnalyticTailData_normalized (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) (A B q : ℝ →ᵇ ℂ)
    (hAB : ∀ t, 0 ≤ t →
      A t=(Real.exp ((2*(j : ℝ))*t) : ℂ)*(spectralDiagonalCoefficient m (q t)-
        spectralDiagonalCoefficient m (boundedRadialPolynomial P t)) ∧
      B t=(Real.exp ((2*(j : ℝ))*t) : ℂ)*(spectralCrossCoefficient m (q t)-
        spectralCrossCoefficient m (boundedRadialPolynomial P t)))
    (lam : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    let U := spectralOutgoingPolynomial (νp-2*lam) (νm-2*lam) η m P c j
    Real.exp (-(2*(j : ℝ))*t) •
        circularTailEvaluation (spectralAnalyticTailData νp νm η m P c j A B lam) t=
      (circularBoundedField (νp-2*lam) (νm-2*lam) η m (q t) (circularPolynomialJet U t)-
        circularBoundedField (νp-2*lam) (νm-2*lam) η m
          (radialExteriorPolynomialFunction P t) (circularPolynomialJet U t))-
        circularPolynomialResidualJet (νp-2*lam) (νm-2*lam) η m P U t := by
  intro U
  have he := circularCoefficientForcing_normalized A B
    (boundedRadialPolynomial U.1) (boundedRadialPolynomial U.2)
    (νp-2*lam) (νm-2*lam) η m (2*(j : ℝ)) t (q t) (boundedRadialPolynomial P t)
    (circularPolynomialJet U t)
    (boundedRadialPolynomial_nonneg U.1 t ht) (boundedRadialPolynomial_nonneg U.2 t ht)
    (hAB t ht).1 (hAB t ht).2
  have hexp : Real.exp (-(2*(j : ℝ))*t)*Real.exp ((2*(j : ℝ))*t)=1 := by
    rw [← Real.exp_add]
    simp
  change Real.exp (-(2*(j : ℝ))*t) •
    (circularTailEvaluation (circularCoefficientForcing A B
      (boundedRadialPolynomial U.1) (boundedRadialPolynomial U.2)) t+
     circularTailEvaluation (spectralNormalizedResidual (νp-2*lam) (νm-2*lam) η m P c j) t)=_
  rw [smul_add,he,smul_smul,hexp,one_smul,spectralNormalizedResidual_eq _ _ _ _ _ _ _ t ht,
    boundedRadialPolynomial_nonneg P t ht]
  rfl

end DefocusingNLS

end OAI
