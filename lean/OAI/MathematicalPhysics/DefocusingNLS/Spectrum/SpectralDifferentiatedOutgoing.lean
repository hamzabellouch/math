import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingParameterBalance

namespace OAI

/-! The actual outgoing construction solves the differentiated spectral
equation on its open contraction region. -/

open Filter Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_differentiated_circular_outgoing (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) (hj : 0 < j)
    (q e : ℝ →ᵇ ℂ)
    (hqe : ∀ t, 0 ≤ t → q t - radialExteriorPolynomialFunction P t =
      (Real.exp (-(2 * (j : ℝ)) * t) : ℂ) * e t) :
    ∃ Y : ℂ → ℝ → E₄,
      (∀ z, circularFieldBound (νp - 2 * z) (νm - 2 * z) η m ‖q‖ < 2 * (j : ℝ) →
        ∀ t, AnalyticAt ℂ (fun lam => Y lam t) z) ∧
      (∀ lam, circularFieldBound (νp - 2 * lam) (νm - 2 * lam) η m ‖q‖ < 2 * (j : ℝ) →
        ∀ t, 0 ≤ t → HasDerivAt (Y lam)
          (circularLeadingField t (Y lam t) +
            circularBoundedField (νp - 2 * lam) (νm - 2 * lam) η m (q t) (Y lam t)) t) ∧
      (∀ lam, Tendsto (Y lam) atTop (nhds ((c.1, 0), (c.2, 0)))) ∧
      (∀ lam, ∃ v : CircularTailSpace, ∀ t,
        Y lam t = circularPolynomialJet
          (spectralOutgoingPolynomial (νp - 2 * lam) (νm - 2 * lam) η m P c j) t +
          circularUnweight (2 * (j : ℝ)) v t) ∧
      (∀ z, circularFieldBound (νp - 2 * z) (νm - 2 * z) η m ‖q‖ < 2 * (j : ℝ) →
        ∀ t, 0 ≤ t → HasDerivAt (fun s => deriv (fun lam => Y lam s) z)
          (circularLeadingField t (deriv (fun lam => Y lam t) z) +
            circularBoundedField (νp - 2 * z) (νm - 2 * z) η m (q t)
              (deriv (fun lam => Y lam t) z) + circularPointSlopeCLM νp νm z (Y z t)) t) := by
  let κ : ℝ := 2 * (j : ℝ)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨A, B, hAB⟩ := exists_bounded_normalized_coefficients m κ q (boundedRadialPolynomial P) e (by
    intro t ht
    simpa only [boundedRadialPolynomial_nonneg P t ht] using hqe t ht)
  let r := spectralAnalyticTailData νp νm η m P c j A B
  let v := circularResolvedCorrection κ hκ νp νm η m hm q r
  let U := fun lam => spectralOutgoingPolynomial (νp - 2 * lam) (νm - 2 * lam) η m P c j
  let Y := fun lam t => circularPolynomialJet (U lam) t + circularUnweight κ (v lam) t
  have hr (z : ℂ) : AnalyticAt ℂ r z := spectralAnalyticTailData_analyticAt νp νm η m P c j A B z
  have hcoef (z : ℂ) (k : ℕ) := spectralOutgoingPolynomial_coeff_analytic
    (fun lam => νp - 2 * lam) (fun lam => νm - 2 * lam) η m P c z
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) j k
  have hdeg (lam : ℂ) := spectralOutgoingPolynomial_degree
    (νp - 2 * lam) (νm - 2 * lam) η m P c j
  have hpoly (z : ℂ) (t : ℝ) := circularPolynomialJet_hasParameterDerivAt
    (fun lam => (U lam).1) (fun lam => (U lam).2) j z
    (fun lam => (hdeg lam).1) (fun lam => (hdeg lam).2)
    (fun k => (hcoef z k).1) (fun k => (hcoef z k).2) t
  have hvan (z : ℂ) (hz : circularFieldBound (νp - 2 * z) (νm - 2 * z) η m ‖q‖ < κ) :
      AnalyticAt ℂ v z := circularResolvedCorrection_analyticAt κ hκ νp νm η m hm q r z (hr z) hz
  refine ⟨Y, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz t
    have hp : AnalyticAt ℂ (fun lam : ℂ => νp - 2 * lam) z :=
      analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
    have hm' : AnalyticAt ℂ (fun lam : ℂ => νm - 2 * lam) z :=
      analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
    exact (spectralPolynomialJet_analyticAt _ _ η m P c j z t hp hm').add
      (circularUnweight_analyticAt κ t v z (hvan z hz))
  · intro lam hlam t ht
    apply circularPolynomial_corrected (νp - 2 * lam) (νm - 2 * lam) η m P (U lam)
      (circularUnweight κ (v lam)) (q t) t
    have hd := circularResolvedCorrection_hasDerivAt κ hκ νp νm η m hm q r lam hlam t
    have hu := circularUnweight_hasDerivAt κ t (νp - 2 * lam) (νm - 2 * lam) η m (q t)
      (v lam) (circularTailEvaluation (r lam) t) hd
    have he := spectralAnalyticTailData_normalized νp νm η m P c j A B q hAB lam t ht
    change Real.exp (-κ * t) • circularTailEvaluation (r lam) t = _ at he
    simpa only [he, add_sub_assoc] using hu
  · intro lam
    have hc := spectralOutgoingPolynomial_constant (νp - 2 * lam) (νm - 2 * lam) η m P c j
    have he := (circularPolynomialJet_tendsto (U lam)).add (circularUnweight_tendsto κ hκ (v lam))
    simpa only [U, hc.1, hc.2, add_zero] using he
  · intro lam
    exact ⟨v lam, fun _ => rfl⟩
  · intro z hz t ht
    have heq : (fun s => deriv (fun lam => Y lam s) z) =
        fun s => circularPolynomialJet
          (polynomialParameterDerivative (fun lam => (U lam).1) j z,
            polynomialParameterDerivative (fun lam => (U lam).2) j z) s +
          circularUnweight κ (deriv v z) s := by
      funext s
      exact ((hpoly z s).add (circularUnweight_hasParameterDerivAt κ s v (deriv v z) z
        (hvan z hz).differentiableAt.hasDerivAt)).deriv
    have hs (lam : ℂ) := circularPolynomial_source_balance (νp - 2 * lam) (νm - 2 * lam)
      η m P (U lam) (q t) κ t (r lam)
      (spectralAnalyticTailData_normalized νp νm η m P c j A B q hAB lam t ht)
    have hd := circularOutgoing_parameter_equation κ hκ νp νm η m hm q
      (fun lam => (U lam).1) (fun lam => (U lam).2) j z
      (fun lam => (hdeg lam).1) (fun lam => (hdeg lam).2)
      (fun k => (hcoef z k).1) (fun k => (hcoef z k).2) r (hr z) hz t hs
    simp only [heq, congrFun heq t]
    simpa only [Y] using hd

end DefocusingNLS

end OAI
