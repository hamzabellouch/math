import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace OAI

/-! # Formal partial derivatives are the actual differential -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial
open scoped BigOperators

def polynomialDifferential {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ j, MvPolynomial.eval x (pderiv j p) • ContinuousLinearMap.proj j

theorem hasFDerivAt_mvPolynomial_eval {m : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) :
    HasFDerivAt (fun y => MvPolynomial.eval y p) (polynomialDifferential p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simpa [polynomialDifferential, pderiv_C] using hasFDerivAt_const c x
  | add p q hp hq =>
      convert hp.add hq using 1
      · ext y; simp
      · simp [polynomialDifferential, add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
      convert hp.mul (hasFDerivAt_apply j x) using 1
      · ext y; simp
      · ext v
        simp [polynomialDifferential, Pi.single_apply, add_mul,
          Finset.sum_add_distrib, Finset.mul_sum, apply_ite, ite_mul, mul_assoc]

theorem fderiv_mvPolynomial_eval {m : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) :
    fderiv ℝ (fun y => MvPolynomial.eval y p) x = polynomialDifferential p x :=
  (hasFDerivAt_mvPolynomial_eval p x).fderiv

theorem polynomialDifferential_basis {m : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) (j : Fin m) :
    polynomialDifferential p x (Pi.single j 1) = MvPolynomial.eval x (pderiv j p) := by
  classical
  simp [polynomialDifferential, Pi.single_apply]

end PolycyclicRecognition

end

end OAI
