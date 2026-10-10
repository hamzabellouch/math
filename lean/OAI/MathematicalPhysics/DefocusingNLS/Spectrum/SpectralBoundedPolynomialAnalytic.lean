import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialAnalytic
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialTailData

namespace OAI

/-! Finite holomorphic coefficient families define holomorphic bounded exterior data. -/

open Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem boundedRadialPolynomial_finite (P : ℂ[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    boundedRadialPolynomial P=
      ∑ k ∈ Finset.range (d+1), P.coeff k • boundedRadialPolynomial (X^k) := by
  apply BoundedContinuousFunction.ext
  intro t
  change P.eval (radialExteriorClampedVariable t : ℂ)=
    (BoundedContinuousFunction.evalCLM ℂ t)
      (∑ k ∈ Finset.range (d+1), P.coeff k • boundedRadialPolynomial (X^k))
  simp only [map_sum,map_smul,BoundedContinuousFunction.evalCLM_apply,
    boundedRadialPolynomial_apply,smul_eq_mul,eval_pow,eval_X]
  exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd) _

theorem boundedRadialPolynomial_analyticAt (P : ℂ → ℂ[X]) (d : ℕ) (z : ℂ)
    (hd : ∀ lam, (P lam).natDegree ≤ d)
    (hP : ∀ k, AnalyticAt ℂ (fun lam => (P lam).coeff k) z) :
    AnalyticAt ℂ (fun lam => boundedRadialPolynomial (P lam)) z := by
  have he : (fun lam => boundedRadialPolynomial (P lam))=
      fun lam => ∑ k ∈ Finset.range (d+1), (P lam).coeff k • boundedRadialPolynomial (X^k) := by
    funext lam
    exact boundedRadialPolynomial_finite (P lam) d (hd lam)
  rw [he]
  exact (Finset.range (d+1)).analyticAt_fun_sum (fun k _ => (hP k).smul analyticAt_const)

theorem polynomial_eval_analyticAt (P : ℂ → ℂ[X]) (d : ℕ) (z x : ℂ)
    (hd : ∀ lam, (P lam).natDegree ≤ d)
    (hP : ∀ k, AnalyticAt ℂ (fun lam => (P lam).coeff k) z) :
    AnalyticAt ℂ (fun lam => (P lam).eval x) z := by
  have he : (fun lam => (P lam).eval x)=
      fun lam => ∑ k ∈ Finset.range (d+1), (P lam).coeff k*x^k := by
    funext lam
    exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hd lam)) x
  rw [he]
  exact (Finset.range (d+1)).analyticAt_fun_sum (fun k _ => (hP k).mul analyticAt_const)

theorem spectralPolynomialJet_analyticAt (νp νm : ℂ → ℂ) (η : ℂ)
    (m : ℕ) (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) (z : ℂ) (t : ℝ)
    (hp : AnalyticAt ℂ νp z) (hm : AnalyticAt ℂ νm z) :
    AnalyticAt ℂ (fun lam => circularPolynomialJet
      (spectralOutgoingPolynomial (νp lam) (νm lam) η m P c j) t) z := by
  let U := fun lam => spectralOutgoingPolynomial (νp lam) (νm lam) η m P c j
  have hd (lam : ℂ) := spectralOutgoingPolynomial_degree (νp lam) (νm lam) η m P c j
  have hc (k : ℕ) := spectralOutgoingPolynomial_coeff_analytic νp νm η m P c z hp hm j k
  have hEuler (Q : ℂ[X]) (hQ : Q.natDegree ≤ j) : (radialPolynomialEuler Q).natDegree ≤ j := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [radialPolynomialEuler_coeff,coeff_eq_zero_of_natDegree_lt (hQ.trans_lt hk),mul_zero]
  have h1 := polynomial_eval_analyticAt (fun lam => (U lam).1) j z
    (Real.exp (-2*t) : ℂ) (fun lam => (hd lam).1) (fun k => (hc k).1)
  have h2 := polynomial_eval_analyticAt (fun lam => (U lam).2) j z
    (Real.exp (-2*t) : ℂ) (fun lam => (hd lam).2) (fun k => (hc k).2)
  have h1' := polynomial_eval_analyticAt (fun lam => radialPolynomialEuler (U lam).1) j z
    (Real.exp (-2*t) : ℂ) (fun lam => hEuler _ (hd lam).1) (fun k => by
      simp only [radialPolynomialEuler_coeff]
      exact analyticAt_const.mul (hc k).1)
  have h2' := polynomial_eval_analyticAt (fun lam => radialPolynomialEuler (U lam).2) j z
    (Real.exp (-2*t) : ℂ) (fun lam => hEuler _ (hd lam).2) (fun k => by
      simp only [radialPolynomialEuler_coeff]
      exact analyticAt_const.mul (hc k).2)
  exact (h1.prod h1').prod (h2.prod h2')

end DefocusingNLS

end OAI
