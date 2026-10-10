import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Transvection
import OAI.Analysis.Laughlin.Spin.BinomialWeights

namespace OAI

namespace Laughlin.Rotation
open Polynomial
open scoped BigOperators Matrix

noncomputable def upperSpinCurve (Q : ℕ) :
    Matrix (Fin (Q+1)) (Fin (Q+1)) (Polynomial ℂ) := fun p q =>
  monomial (q.val-p.val) (spinBinomialWeight Q q / spinBinomialWeight Q p *
    (q.val.choose p.val : ℂ))

theorem upperSpinCurve_eval (Q : ℕ) (c : ℂ) (p q : Fin (Q+1)) :
    (upperSpinCurve Q p q).eval c =
      generalSpinMatrix Q (Matrix.transvection (0 : Fin 2) 1 c) p q := by
  let M := generalSpinMatrix Q (Matrix.transvection (0 : Fin 2) 1 c)
  have h := generalSpinMatrix_polynomial Polynomial.C Q
    (Matrix.transvection (0 : Fin 2) 1 c) (1 : Polynomial ℂ) X q
  have he : (∑ r : Fin (Q+1), C (M r q) * (C (spinBinomialWeight Q r) * X^r.val)) =
      C (spinBinomialWeight Q q) * (X+C c)^q.val := by
    simpa [M,spinBinomialWeight,Matrix.transvection,Matrix.single,Matrix.one_apply,add_comm] using h
  have hc := congrArg (fun P : Polynomial ℂ => P.coeff p.val) he
  simp only [finsetSum_coeff,coeff_C_mul,coeff_X_pow,mul_ite,mul_one,mul_zero,
    coeff_X_add_C_pow] at hc
  simp only [← Fin.ext_iff,Finset.sum_ite_eq,Finset.mem_univ,ite_true] at hc
  apply (mul_right_cancel₀ (spinBinomialWeight_ne_zero Q p))
  change (upperSpinCurve Q p q).eval c * spinBinomialWeight Q p = M p q * spinBinomialWeight Q p
  rw [hc]
  simp only [upperSpinCurve,eval_monomial]
  field_simp [spinBinomialWeight_ne_zero Q p]

theorem upperSpinCurve_zero (Q : ℕ) (p q : Fin (Q+1)) :
    (upperSpinCurve Q p q).coeff 0 = if p=q then 1 else 0 := by
  rw [coeff_zero_eq_eval_zero,upperSpinCurve_eval,Matrix.transvection_zero,generalSpinMatrix_one,
    Matrix.one_apply]

theorem upperSpinCurve_derivative_zero (Q : ℕ) (p : Fin (Q+1)) :
    (upperSpinCurve Q p 0).derivative = 0 := by
  simp [upperSpinCurve]

theorem upperSpinCurve_derivative_succ (Q : ℕ) (p : Fin (Q+1)) (q : Fin Q) :
    (upperSpinCurve Q p q.succ).derivative =
      upperSpinCurve Q p q.castSucc * C (Spin.ladder Q q.val : ℂ) := by
  by_cases hp : p.val ≤ q.val
  · have he : q.val+1-p.val-1=q.val-p.val := by omega
    simp only [upperSpinCurve,Fin.val_succ,Fin.val_castSucc,derivative_monomial,
      monomial_mul_C,he]
    congr 1
    have hc := congrArg (fun n : ℕ => (n : ℂ)) (Nat.choose_mul_succ_eq q.val p.val)
    push_cast at hc
    have hw := spinBinomialWeight_step Q q
    field_simp [spinBinomialWeight_ne_zero Q p]
    linear_combination -(spinBinomialWeight Q q.succ)*hc +
      (q.val.choose p.val : ℂ)*hw
  · have hsmall : q.val < p.val := by omega
    by_cases hlarge : q.val+1 < p.val
    · simp [upperSpinCurve,Nat.choose_eq_zero_of_lt hsmall,Nat.choose_eq_zero_of_lt hlarge]
    · have he : p.val=q.val+1 := by omega
      simp [upperSpinCurve,he]

end Laughlin.Rotation

end OAI
