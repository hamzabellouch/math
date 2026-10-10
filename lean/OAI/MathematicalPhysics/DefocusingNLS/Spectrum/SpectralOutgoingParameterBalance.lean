import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPointFieldParameter
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialMixedDerivative

namespace OAI

/-! The differentiated polynomial and correction sources cancel in the actual
outgoing construction. -/

open Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularPolynomial_source_balance (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (U : ℂ[X] × ℂ[X]) (q : ℂ) (κ t : ℝ)
    (r : CircularTailSpace)
    (hr : circularUnweight κ r t =
      (circularBoundedField νp νm η m q (circularPolynomialJet U t) -
        circularBoundedField νp νm η m (radialExteriorPolynomialFunction P t)
          (circularPolynomialJet U t)) - circularPolynomialResidualJet νp νm η m P U t) :
    circularUnweight κ r t +
        circularPolynomialJet (radialPolynomialEuler U.1, radialPolynomialEuler U.2) t =
      circularLeadingField t (circularPolynomialJet U t) +
        circularBoundedField νp νm η m q (circularPolynomialJet U t) := by
  have hd := (circularPolynomialJet_time_hasDerivAt U.1 U.2 t).unique
    (circularPolynomialJet_hasDerivAt νp νm η m P U t)
  rw [hr, hd]
  abel

theorem circularPolynomial_source_parameter_balance (νp νm η : ℂ) (m : ℕ)
    (q z : ℂ) (κ t : ℝ) (P Q : ℂ → ℂ[X]) (d : ℕ)
    (hPd : ∀ lam, (P lam).natDegree ≤ d) (hQd : ∀ lam, (Q lam).natDegree ≤ d)
    (hP : ∀ k, AnalyticAt ℂ (fun lam => (P lam).coeff k) z)
    (hQ : ∀ k, AnalyticAt ℂ (fun lam => (Q lam).coeff k) z)
    (r : ℂ → CircularTailSpace) (hr : AnalyticAt ℂ r z)
    (hsource : ∀ lam, circularUnweight κ (r lam) t +
        circularPolynomialJet (radialPolynomialEuler (P lam), radialPolynomialEuler (Q lam)) t =
      circularLeadingField t (circularPolynomialJet (P lam, Q lam) t) +
        circularBoundedField (νp - 2 * lam) (νm - 2 * lam) η m q
          (circularPolynomialJet (P lam, Q lam) t)) :
    let D := (polynomialParameterDerivative P d z, polynomialParameterDerivative Q d z)
    circularUnweight κ (deriv r z) t +
        circularPolynomialJet (radialPolynomialEuler D.1, radialPolynomialEuler D.2) t =
      circularLeadingField t (circularPolynomialJet D t) +
        circularBoundedField (νp - 2 * z) (νm - 2 * z) η m q (circularPolynomialJet D t) +
        circularPointSlopeCLM νp νm z (circularPolynomialJet (P z, Q z) t) := by
  let D := (polynomialParameterDerivative P d z, polynomialParameterDerivative Q d z)
  have hEd (A : ℂ[X]) (hA : A.natDegree ≤ d) : (radialPolynomialEuler A).natDegree ≤ d := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [radialPolynomialEuler_coeff, coeff_eq_zero_of_natDegree_lt (hA.trans_lt hk), mul_zero]
  have hPe (k : ℕ) : AnalyticAt ℂ (fun lam => (radialPolynomialEuler (P lam)).coeff k) z := by
    simp only [radialPolynomialEuler_coeff]
    exact analyticAt_const.mul (hP k)
  have hQe (k : ℕ) : AnalyticAt ℂ (fun lam => (radialPolynomialEuler (Q lam)).coeff k) z := by
    simp only [radialPolynomialEuler_coeff]
    exact analyticAt_const.mul (hQ k)
  have hu := circularPolynomialJet_hasParameterDerivAt P Q d z hPd hQd hP hQ t
  have he := circularPolynomialJet_hasParameterDerivAt
    (fun lam => radialPolynomialEuler (P lam)) (fun lam => radialPolynomialEuler (Q lam))
    d z (fun lam => hEd _ (hPd lam)) (fun lam => hEd _ (hQd lam)) hPe hQe t
  rw [polynomialParameterDerivative_euler P d z hP, polynomialParameterDerivative_euler Q d z hQ] at he
  have hl := (circularUnweight_hasParameterDerivAt κ t r (deriv r z) z
    hr.differentiableAt.hasDerivAt).add he
  have hright := (circularPointLeading_hasParameterDerivAt t _ _ z hu).add
    (circularPointField_hasParameterDerivAt νp νm η m q z _ _ hu)
  have hleft := hl.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun lam => (hsource lam).symm))
  have hh := hleft.unique hright
  change circularUnweight κ (deriv r z) t +
        circularPolynomialJet (radialPolynomialEuler D.1, radialPolynomialEuler D.2) t = _
  simpa only [add_assoc] using hh

theorem circularCorrection_parameter_source (κ : ℝ) (νp νm η : ℂ) (m : ℕ)
    (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ) (z : ℂ) (v r : CircularTailSpace) (t : ℝ) :
    Real.exp (-κ * t) • circularTailEvaluation
        (circularFieldParameterSlope νp νm η m hm q z v + r) t =
      circularPointSlopeCLM νp νm z (circularUnweight κ v t) + circularUnweight κ r t := by
  change Real.exp (-κ * t) •
      (circularTailEvaluation (circularFieldParameterSlope νp νm η m hm q z v) t +
        circularTailEvaluation r t) = _
  rw [smul_add, circularPointSlope_tail]
  change Real.exp (-κ * t) • circularPointSlopeCLM νp νm z (circularTailEvaluation v t) +
      circularUnweight κ r t =
    circularPointSlopeCLM νp νm z (Real.exp (-κ * t) • circularTailEvaluation v t) +
      circularUnweight κ r t
  exact congrArg (fun w => w + circularUnweight κ r t)
    (((circularPointSlopeCLM νp νm z).restrictScalars ℝ).map_smul
      (Real.exp (-κ * t)) (circularTailEvaluation v t)).symm

theorem circularOutgoing_parameter_equation (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ)
    (P Q : ℂ → ℂ[X]) (d : ℕ) (z : ℂ)
    (hPd : ∀ lam, (P lam).natDegree ≤ d) (hQd : ∀ lam, (Q lam).natDegree ≤ d)
    (hP : ∀ k, AnalyticAt ℂ (fun lam => (P lam).coeff k) z)
    (hQ : ∀ k, AnalyticAt ℂ (fun lam => (Q lam).coeff k) z)
    (r : ℂ → CircularTailSpace) (hr : AnalyticAt ℂ r z)
    (hgap : circularFieldBound (νp - 2 * z) (νm - 2 * z) η m ‖q‖ < κ)
    (t : ℝ)
    (hsource : ∀ lam, circularUnweight κ (r lam) t +
        circularPolynomialJet (radialPolynomialEuler (P lam), radialPolynomialEuler (Q lam)) t =
      circularLeadingField t (circularPolynomialJet (P lam, Q lam) t) +
        circularBoundedField (νp - 2 * lam) (νm - 2 * lam) η m (q t)
          (circularPolynomialJet (P lam, Q lam) t)) :
    let v := circularResolvedCorrection κ hκ νp νm η m hm q r
    let D := (polynomialParameterDerivative P d z, polynomialParameterDerivative Q d z)
    let dY := fun s => circularPolynomialJet D s + circularUnweight κ (deriv v z) s
    let Y := circularPolynomialJet (P z, Q z) t + circularUnweight κ (v z) t
    HasDerivAt dY
      (circularLeadingField t (dY t) +
        circularBoundedField (νp - 2 * z) (νm - 2 * z) η m (q t) (dY t) +
        circularPointSlopeCLM νp νm z Y) t := by
  let v := circularResolvedCorrection κ hκ νp νm η m hm q r
  let D := (polynomialParameterDerivative P d z, polynomialParameterDerivative Q d z)
  have hb := circularPolynomial_source_parameter_balance νp νm η m (q t) z κ t
    P Q d hPd hQd hP hQ r hr hsource
  have hc := circularResolvedCorrection_parameter_unweight_equation κ hκ
    νp νm η m hm q r z hr hgap t
  dsimp only at hc
  rw [circularCorrection_parameter_source] at hc
  have hp := circularPolynomialJet_time_hasDerivAt D.1 D.2 t
  apply (hp.add hc).congr_deriv
  dsimp only
  rw [circularLeadingField_add, circularBoundedField_add, map_add]
  change circularPolynomialJet (radialPolynomialEuler D.1, radialPolynomialEuler D.2) t +
      (circularLeadingField t (circularUnweight κ (deriv v z) t) +
        circularBoundedField (νp - 2 * z) (νm - 2 * z) η m (q t)
          (circularUnweight κ (deriv v z) t) +
        (circularPointSlopeCLM νp νm z (circularUnweight κ (v z) t) +
          circularUnweight κ (deriv r z) t)) = _
  calc
    _ = (circularUnweight κ (deriv r z) t +
        circularPolynomialJet (radialPolynomialEuler D.1, radialPolynomialEuler D.2) t) +
        (circularLeadingField t (circularUnweight κ (deriv v z) t) +
          circularBoundedField (νp - 2 * z) (νm - 2 * z) η m (q t)
            (circularUnweight κ (deriv v z) t) +
          circularPointSlopeCLM νp νm z (circularUnweight κ (v z) t)) := by abel
    _ = _ := by rw [hb]; abel

end DefocusingNLS

end OAI
