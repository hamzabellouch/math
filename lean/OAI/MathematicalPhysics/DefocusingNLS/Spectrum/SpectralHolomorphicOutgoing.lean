import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAnalyticTailData
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAnalyticCorrection

namespace OAI

/-! The actual outgoing columns are locally holomorphic on every contracting parameter region. -/

open Filter Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def circularTailEvaluationCLM (t : ℝ) : CircularTailSpace →L[ℂ] E₄ :=
  ((BoundedContinuousFunction.evalCLM ℂ t).comp
      (ContinuousLinearMap.fst ℂ (ℝ →ᵇ ℂ × ℂ) (ℝ →ᵇ ℂ × ℂ))).prod
    ((BoundedContinuousFunction.evalCLM ℂ t).comp
      (ContinuousLinearMap.snd ℂ (ℝ →ᵇ ℂ × ℂ) (ℝ →ᵇ ℂ × ℂ)))

theorem circularUnweight_analyticAt (κ t : ℝ) (v : ℂ → CircularTailSpace) (z : ℂ)
    (hv : AnalyticAt ℂ v z) :
    AnalyticAt ℂ (fun lam => circularUnweight κ (v lam) t) z := by
  have he : (fun lam => circularUnweight κ (v lam) t)=
      fun lam => (Real.exp (-κ*t) : ℂ) • circularTailEvaluationCLM t (v lam) := by
    funext lam
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [circularUnweight,circularTailEvaluation,circularTailEvaluationCLM,
        ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
        BoundedContinuousFunction.evalCLM_apply,Prod.smul_mk,Prod.smul_fst,Prod.smul_snd,
        Complex.real_smul,smul_eq_mul]
  rw [he]
  have hc : AnalyticAt ℂ (fun _ : ℂ => (Real.exp (-κ*t) : ℂ)) z := analyticAt_const
  convert! hc.smul (((circularTailEvaluationCLM t).analyticAt (v z)).comp hv)

theorem exists_holomorphic_circular_outgoing (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) (hj : 0 < j)
    (q e : ℝ →ᵇ ℂ)
    (hqe : ∀ t, 0 ≤ t → q t-radialExteriorPolynomialFunction P t=
      (Real.exp (-(2*(j : ℝ))*t) : ℂ)*e t) :
    ∃ Y : ℂ → ℝ → E₄,
      (∀ z, circularFieldBound (νp-2*z) (νm-2*z) η m ‖q‖ < 2*(j : ℝ) →
        ∀ t, AnalyticAt ℂ (fun lam => Y lam t) z) ∧
      (∀ lam, circularFieldBound (νp-2*lam) (νm-2*lam) η m ‖q‖ < 2*(j : ℝ) →
        ∀ t, 0 ≤ t → HasDerivAt (Y lam)
          (circularLeadingField t (Y lam t)+
            circularBoundedField (νp-2*lam) (νm-2*lam) η m (q t) (Y lam t)) t) ∧
      (∀ lam, Tendsto (Y lam) atTop (nhds ((c.1,0),(c.2,0)))) ∧
      (∀ lam, ∃ v : CircularTailSpace, ∀ t,
        Y lam t=circularPolynomialJet
          (spectralOutgoingPolynomial (νp-2*lam) (νm-2*lam) η m P c j) t+
          circularUnweight (2*(j : ℝ)) v t) := by
  let κ : ℝ := 2*(j : ℝ)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨A,B,hAB⟩ := exists_bounded_normalized_coefficients m κ q (boundedRadialPolynomial P) e (by
    intro t ht
    simpa only [boundedRadialPolynomial_nonneg P t ht] using hqe t ht)
  let r := spectralAnalyticTailData νp νm η m P c j A B
  let v := circularResolvedCorrection κ hκ νp νm η m hm q r
  let U := fun lam => spectralOutgoingPolynomial (νp-2*lam) (νm-2*lam) η m P c j
  let Y := fun lam t => circularPolynomialJet (U lam) t+circularUnweight κ (v lam) t
  refine ⟨Y,?_,?_,?_,?_⟩
  · intro z hz t
    have hp : AnalyticAt ℂ (fun lam : ℂ => νp-2*lam) z :=
      analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
    have hn : AnalyticAt ℂ (fun lam : ℂ => νm-2*lam) z :=
      analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
    have hv : AnalyticAt ℂ v z := circularResolvedCorrection_analyticAt κ hκ
      νp νm η m hm q r z (spectralAnalyticTailData_analyticAt νp νm η m P c j A B z) hz
    exact (spectralPolynomialJet_analyticAt _ _ η m P c j z t hp hn).add
      (circularUnweight_analyticAt κ t v z hv)
  · intro lam hlam t ht
    apply circularPolynomial_corrected (νp-2*lam) (νm-2*lam) η m P (U lam)
      (circularUnweight κ (v lam)) (q t) t
    have hd := circularResolvedCorrection_hasDerivAt κ hκ νp νm η m hm q r lam hlam t
    have hu := circularUnweight_hasDerivAt κ t (νp-2*lam) (νm-2*lam) η m (q t)
      (v lam) (circularTailEvaluation (r lam) t) hd
    have hr := spectralAnalyticTailData_normalized νp νm η m P c j A B q hAB lam t ht
    change Real.exp (-κ*t) • circularTailEvaluation (r lam) t=_ at hr
    simpa only [hr,add_sub_assoc] using hu
  · intro lam
    have hc := spectralOutgoingPolynomial_constant (νp-2*lam) (νm-2*lam) η m P c j
    have hlim := (circularPolynomialJet_tendsto (U lam)).add (circularUnweight_tendsto κ hκ (v lam))
    simpa only [U,hc.1,hc.2,add_zero] using hlim
  · intro lam
    exact ⟨v lam,fun _ => rfl⟩

end DefocusingNLS

end OAI
