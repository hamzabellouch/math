import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundedPolynomialAnalytic
import Mathlib.Algebra.Polynomial.Inductions

namespace OAI

/-! A canonical, holomorphic choice of the normalized finite spectral residual. -/

open Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def spectralDropPolynomial (P : ℂ[X]) (j : ℕ) : ℂ[X] :=
  (Polynomial.divX^[j]) P

theorem spectralDropPolynomial_coeff (P : ℂ[X]) (j k : ℕ) :
    (spectralDropPolynomial P j).coeff k=P.coeff (k+j) := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    rw [spectralDropPolynomial,Function.iterate_succ_apply',coeff_divX]
    change (spectralDropPolynomial P j).coeff (k+1)=_
    rw [ih]
    congr 1
    omega

theorem spectralDropPolynomial_factor (P : ℂ[X]) (j : ℕ) (hj : X^j ∣ P) :
    X^j*spectralDropPolynomial P j=P := by
  obtain ⟨Q,hQ⟩ := hj
  have hdrop : spectralDropPolynomial P j=Q := by
    ext k
    rw [spectralDropPolynomial_coeff,hQ,coeff_X_pow_mul]
  rw [hdrop]
  exact hQ.symm

theorem spectralDropPolynomial_degree (P : ℂ[X]) (j : ℕ) :
    (spectralDropPolynomial P j).natDegree ≤ P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [spectralDropPolynomial_coeff]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem spectralPolynomialResidual_degree (h ν η : ℂ) (A B U V : ℂ[X])
    (j : ℕ) (hU : U.natDegree ≤ j) (hV : V.natDegree ≤ j) :
    (spectralPolynomialResidual h ν η A B U V).natDegree ≤ j+A.natDegree+B.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have hu : U.coeff k=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hu' : U.coeff (k+1)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have ha : (A*U).coeff k=0 := coeff_eq_zero_of_natDegree_lt
    (natDegree_mul_le.trans_lt (by omega))
  have hb : (B*V).coeff k=0 := coeff_eq_zero_of_natDegree_lt
    (natDegree_mul_le.trans_lt (by omega))
  simp only [spectralPolynomialResidual,coeff_sub,coeff_add,coeff_C_mul,
    radialPolynomialEuler_coeff,coeff_derivative,hu,hu',ha,hb,mul_zero,zero_mul,
    add_zero,sub_zero]

theorem boundedRadialResidual_finite (P : ℂ[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    boundedRadialResidual P=
      ∑ k ∈ Finset.range (d+1), P.coeff k • boundedRadialResidual (X^k) := by
  apply BoundedContinuousFunction.ext
  intro t
  change (0,-P.eval (radialExteriorClampedVariable t : ℂ))=
    (BoundedContinuousFunction.evalCLM ℂ t)
      (∑ k ∈ Finset.range (d+1), P.coeff k • boundedRadialResidual (X^k))
  rw [map_sum]
  simp only [map_smul,BoundedContinuousFunction.evalCLM_apply,boundedRadialResidual_apply,
    boundedRadialPolynomial_apply,eval_pow,eval_X,Prod.smul_mk,
    smul_eq_mul,mul_neg]
  apply Prod.ext
  · rw [Prod.fst_sum]
    simp
  · simp only [Prod.snd_sum,Finset.sum_neg_distrib]
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd)]

theorem boundedRadialResidual_analyticAt (P : ℂ → ℂ[X]) (d : ℕ) (z : ℂ)
    (hd : ∀ lam, (P lam).natDegree ≤ d)
    (hP : ∀ k, AnalyticAt ℂ (fun lam => (P lam).coeff k) z) :
    AnalyticAt ℂ (fun lam => boundedRadialResidual (P lam)) z := by
  have he : (fun lam => boundedRadialResidual (P lam))=
      fun lam => ∑ k ∈ Finset.range (d+1), (P lam).coeff k • boundedRadialResidual (X^k) := by
    funext lam
    exact boundedRadialResidual_finite (P lam) d (hd lam)
  rw [he]
  exact (Finset.range (d+1)).analyticAt_fun_sum (fun k _ => (hP k).smul analyticAt_const)

noncomputable def spectralNormalizedResidual (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) : CircularTailSpace :=
  let R := spectralPolynomialResidualPair νp νm η m P
    (spectralOutgoingPolynomial νp νm η m P c j)
  (boundedRadialResidual (spectralDropPolynomial R.1 j),
   boundedRadialResidual (spectralDropPolynomial R.2 j))

theorem spectralNormalizedResidual_eq (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(2*(j : ℝ))*t) •
        circularTailEvaluation (spectralNormalizedResidual νp νm η m P c j) t=
      -circularPolynomialResidualJet νp νm η m P
        (spectralOutgoingPolynomial νp νm η m P c j) t := by
  let R := spectralPolynomialResidualPair νp νm η m P
    (spectralOutgoingPolynomial νp νm η m P c j)
  have hd := spectralOutgoingPolynomial_residual νp νm η m P c j
  have hp := spectralDropPolynomial_factor R.1 j hd.1
  have hm := spectralDropPolynomial_factor R.2 j hd.2
  have he : (Real.exp (-(2*(j : ℝ))*t) : ℂ)=
      (Real.exp (-2*t) : ℂ)^j := by
    rw [← Complex.ofReal_pow,← Real.exp_nat_mul]
    congr 2
    ring
  have hfactor (Q : ℂ[X]) (hQ : X^j*spectralDropPolynomial Q j=Q) :
      radialExteriorPolynomialFunction Q t=
        (Real.exp (-(2*(j : ℝ))*t) : ℂ)*
          radialExteriorPolynomialFunction (spectralDropPolynomial Q j) t := by
    conv_lhs => rw [← hQ]
    simp only [radialExteriorPolynomialFunction,eval_mul,eval_pow,eval_X,he]
  have hp' := hfactor R.1 hp
  have hm' := hfactor R.2 hm
  change Real.exp (-(2*(j : ℝ))*t) •
    ((0,-boundedRadialPolynomial (spectralDropPolynomial R.1 j) t),
     (0,-boundedRadialPolynomial (spectralDropPolynomial R.2 j) t))=
    -((0,radialExteriorPolynomialFunction R.1 t),(0,radialExteriorPolynomialFunction R.2 t))
  simp only [boundedRadialPolynomial_nonneg _ t ht,Prod.smul_mk,Prod.neg_mk,
    smul_zero,neg_zero,Complex.real_smul,mul_neg,hp',hm']

theorem spectralNormalizedResidual_analyticAt (νp νm : ℂ → ℂ) (η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) (z : ℂ)
    (hp : AnalyticAt ℂ νp z) (hm : AnalyticAt ℂ νm z) :
    AnalyticAt ℂ (fun lam => spectralNormalizedResidual (νp lam) (νm lam) η m P c j) z := by
  let U := fun lam => spectralOutgoingPolynomial (νp lam) (νm lam) η m P c j
  let A := spectralDiagonalPolynomial m P
  let B := spectralCrossPolynomial m P
  let A' := Polynomial.mapRingHom (starRingEnd ℂ) A
  let B' := Polynomial.mapRingHom (starRingEnd ℂ) B
  have hU (k : ℕ) := spectralOutgoingPolynomial_coeff_analytic νp νm η m P c z hp hm j k
  have hUd (lam : ℂ) := spectralOutgoingPolynomial_degree (νp lam) (νm lam) η m P c j
  have hplus : AnalyticAt ℂ (fun lam => boundedRadialResidual
      (spectralDropPolynomial (spectralPolynomialResidual 1 (νp lam) η A B
        (U lam).1 (U lam).2) j)) z := by
    apply boundedRadialResidual_analyticAt _ (j+A.natDegree+B.natDegree) z
    · intro lam
      exact (spectralDropPolynomial_degree _ j).trans
        (spectralPolynomialResidual_degree _ _ _ _ _ _ _ j (hUd lam).1 (hUd lam).2)
    · intro k
      simp only [spectralDropPolynomial_coeff]
      exact spectralPolynomialResidual_coeff_analytic 1 η νp A B
        (fun lam => (U lam).1) (fun lam => (U lam).2) z hp
        (fun k => (hU k).1) (fun k => (hU k).2) (k+j)
  have hminus : AnalyticAt ℂ (fun lam => boundedRadialResidual
      (spectralDropPolynomial (spectralPolynomialResidual (-1) (νm lam) η A' B'
        (U lam).2 (U lam).1) j)) z := by
    apply boundedRadialResidual_analyticAt _ (j+A'.natDegree+B'.natDegree) z
    · intro lam
      exact (spectralDropPolynomial_degree _ j).trans
        (spectralPolynomialResidual_degree _ _ _ _ _ _ _ j (hUd lam).2 (hUd lam).1)
    · intro k
      simp only [spectralDropPolynomial_coeff]
      exact spectralPolynomialResidual_coeff_analytic (-1) η νm A' B'
        (fun lam => (U lam).2) (fun lam => (U lam).1) z hm
        (fun k => (hU k).2) (fun k => (hU k).1) (k+j)
  exact hplus.prod hminus

end DefocusingNLS

end OAI
