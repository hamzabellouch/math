import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import OAI.AlgebraicGeometry.PlaneCurves.TaylorMultiplicity

namespace OAI

/-!
# Mixed partial derivatives and ordinary polynomial jets
-/

section

/-! Genuine ordinary mixed analytic derivatives of complex plane polynomials. -/

namespace Nagata.Workers.W30

open MvPolynomial
open scoped BigOperators

/-- The ordinary affine point `(x,y)`. -/
def planePoint (x y : ℂ) : Fin 2 → ℂ := Fin.cases x (fun _ => y)

@[simp] lemma planePoint_zero (x y : ℂ) : planePoint x y 0 = x := rfl
@[simp] lemma planePoint_one (x y : ℂ) : planePoint x y 1 = y := rfl

/-- Evaluate a genuine bivariate polynomial on its two complex coordinates. -/
noncomputable def planeValue (p : Bivariate ℂ) (x y : ℂ) : ℂ :=
  eval (planePoint x y) p

lemma planeValue_monomial (a : Fin 2 →₀ ℕ) (c x y : ℂ) :
    planeValue (monomial a c) x y = c * x ^ (a 0) * y ^ (a 1) := by
  have hmon : (monomial a c : Bivariate ℂ) = C c * monomial a 1 := by
    rw [C_mul_monomial, mul_one]
  rw [planeValue, hmon, ← exponentPair_eta a, monomial_exponentPair]
  simp [mul_assoc]

lemma planeValue_sum (p : Bivariate ℂ) (x y : ℂ) :
    planeValue p x y = ∑ a ∈ p.support, p.coeff a * x ^ (a 0) * y ^ (a 1) := by
  conv_lhs => rw [p.as_sum]
  simp only [planeValue, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact planeValue_monomial a (p.coeff a) x y

/-- Ordinary Y-derivatives at Y=0, retaining the X-variable. -/
lemma innerDerivative_zero (p : Bivariate ℂ) (b : ℕ) (x : ℂ) :
    iteratedDeriv b (fun y => planeValue p x y) 0 =
      ∑ a ∈ p.support, p.coeff a * x ^ (a 0) *
        (if b = a 1 then ((a 1).factorial : ℂ) else 0) := by
  classical
  simp_rw [planeValue_sum]
  rw [iteratedDeriv_fun_sum (fun a _ => contDiffAt_const.mul (contDiffAt_id.pow (a 1)))]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : b = a 1 <;> simp [h]

/-- Take Y-derivatives first, and then X-derivatives, at an ordinary affine point. -/
noncomputable def mixedDerivative (ell b : ℕ) (p : Bivariate ℂ) (x y : ℂ) : ℂ :=
  iteratedDeriv ell (fun z => iteratedDeriv b (fun w => planeValue p z w) y) x

/-- At the origin the actual mixed analytic derivative is factorial times coefficient. -/
theorem mixedDerivative_zero (ell b : ℕ) (p : Bivariate ℂ) :
    mixedDerivative ell b p 0 0 =
      (ell.factorial : ℂ) * (b.factorial : ℂ) * p.coeff (exponentPair ell b) := by
  classical
  unfold mixedDerivative
  simp_rw [innerDerivative_zero]
  rw [iteratedDeriv_fun_sum (fun a _ =>
    (contDiffAt_const.mul (contDiffAt_id.pow (a 0))).mul contDiffAt_const)]
  simp only [iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero]
  rw [Finset.sum_eq_single (exponentPair ell b)]
  · simp [mul_comm, mul_left_comm, mul_assoc]
  · intro a ha hne
    by_cases h0 : ell = a 0
    · by_cases h1 : b = a 1
      · exfalso
        apply hne
        simpa [← h0, ← h1] using (exponentPair_eta a).symm
      · simp [h1]
    · simp [h0]
  · intro hnot
    have hc : p.coeff (exponentPair ell b) = 0 := by
      simpa only [mem_support_iff, not_not] using hnot
    simp [hc]

lemma planePoint_add (x y u v : ℂ) :
    planePoint x y + planePoint u v = planePoint (x+u) (y+v) := by
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

lemma planePoint_eta (v : Fin 2 → ℂ) : planePoint (v 0) (v 1) = v := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

lemma planeValue_translate (p : Bivariate ℂ) (x y u v : ℂ) :
    planeValue (Nagata.AffineMultiplicity.translateHom (planePoint x y) p) u v =
      planeValue p (u+x) (v+y) := by
  unfold planeValue
  rw [Nagata.AffineMultiplicity.eval_translate, planePoint_add]

/-- Translation commutes with actual ordinary mixed derivatives. -/
lemma mixedDerivative_translate_zero (ell b : ℕ) (p : Bivariate ℂ) (x y : ℂ) :
    mixedDerivative ell b
      (Nagata.AffineMultiplicity.translateHom (planePoint x y) p) 0 0 =
      mixedDerivative ell b p x y := by
  unfold mixedDerivative
  simp_rw [planeValue_translate]
  simp only [iteratedDeriv_comp_add_const, zero_add]
  simpa only [zero_add] using congrFun (iteratedDeriv_comp_add_const ell
    (fun z => iteratedDeriv b (planeValue p z) y) x) 0

/-- Exact factorial bridge between ordinary analytic derivatives and translated
polynomial coefficients at every affine point. All orders, including zero, are retained. -/
theorem mixedDerivative_eq_translated_coefficient (ell b : ℕ) (p : Bivariate ℂ)
    (v : Fin 2 → ℂ) :
    mixedDerivative ell b p (v 0) (v 1) =
      (ell.factorial : ℂ) * (b.factorial : ℂ) *
        (Nagata.AffineMultiplicity.translateHom v p).coeff (exponentPair ell b) := by
  rw [← mixedDerivative_translate_zero, mixedDerivative_zero, planePoint_eta]

end Nagata.Workers.W30

end

end OAI
