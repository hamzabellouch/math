import Mathlib
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.PolynomialPoleBound

variable {K C σ : Type*} [Field K] [CommRing C] [Algebra C K]

def realValuation (v : AddValuation K (WithTop ℤ)) : AddValuation K (WithTop ℝ) :=
  v.map (Int.castAddHom ℝ).withTopMap rfl
    ((show Monotone (fun z : ℤ => (z : ℝ)) from Int.cast_mono).withTop_map)

@[simp] theorem realValuation_apply (v : AddValuation K (WithTop ℤ)) (x : K) :
    realValuation v x = WithTop.map (fun z : ℤ => (z : ℝ)) (v x) := rfl

theorem valuation_prod (v : AddValuation K (WithTop ℝ))
    (s : Finset σ) (f : σ → K) : v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

theorem monomial_order_lower (v : AddValuation K (WithTop ℝ))
    (x : σ → K) (w : σ → ℝ) (D : ℝ)
    (hx : ∀ i, ((-w i * D : ℝ) : WithTop ℝ) ≤ v (x i))
    (hc : ∀ c : C, (0 : WithTop ℝ) ≤ v (algebraMap C K c))
    (d : σ →₀ ℕ) (c : C) :
    ((-Finsupp.weight w d * D : ℝ) : WithTop ℝ) ≤
      v (MvPolynomial.aeval x (MvPolynomial.monomial d c)) := by
  classical
  rw [MvPolynomial.aeval_monomial, v.map_mul, Finsupp.prod, valuation_prod]
  have heq : ((-Finsupp.weight w d * D : ℝ) : WithTop ℝ) =
      ∑ i ∈ d.support, d i • ((-w i * D : ℝ) : WithTop ℝ) := by
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_sum]
    apply congrArg (fun r : ℝ => (r : WithTop ℝ))
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
      Finset.sum_mul, neg_mul]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  calc
    (∑ i ∈ d.support, d i • ((-w i * D : ℝ) : WithTop ℝ)) ≤
      ∑ i ∈ d.support, v (x i ^ d i) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [v.map_pow]
        exact nsmul_le_nsmul_right (hx i) (d i)
    _ ≤ v (algebraMap C K c) + ∑ i ∈ d.support, v (x i ^ d i) :=
      le_add_of_nonneg_left (hc c)

theorem polynomial_order_lower (v : AddValuation K (WithTop ℝ))
    (x : σ → K) (w : σ → ℝ) (D N : ℝ) (hD : 0 ≤ D)
    (hx : ∀ i, ((-w i * D : ℝ) : WithTop ℝ) ≤ v (x i))
    (hc : ∀ c : C, (0 : WithTop ℝ) ≤ v (algebraMap C K c))
    (p : MvPolynomial σ C)
    (hp : ∀ d ∈ p.support, Finsupp.weight w d ≤ N) :
    ((-N * D : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.aeval x p) := by
  classical
  rw [p.as_sum, map_sum]
  apply v.map_le_sum
  intro d hd
  have hnum : -N * D ≤ -Finsupp.weight w d * D :=
    mul_le_mul_of_nonneg_right (neg_le_neg (hp d hd)) hD
  exact (WithTop.coe_le_coe.mpr hnum).trans (monomial_order_lower v x w D hx hc d _)

theorem framePolynomial_order_lower {m : ℕ} [Algebra ℂ K]
    (v : AddValuation K (WithTop ℝ)) (x : Fin (m+1) → K)
    (w : Fin (m+1) → ℝ) (D N : ℝ) (hD : 0 ≤ D)
    (hx : ∀ i, ((-w i * D : ℝ) : WithTop ℝ) ≤ v (x i))
    (hc : ∀ c : ℂ, (0 : WithTop ℝ) ≤ v (algebraMap ℂ K c))
    (p : MvPolynomial (Fin (m+1)) ℂ) (hp : PiExponentApprox.HasWeightedDegreeLE w N p) :
    ((-N * D : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.aeval x p) := by
  apply polynomial_order_lower v x w D N hD hx hc p
  intro d hd
  simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, PiExponentApprox.monomialWeight] using hp d hd

end PiExponent.PolynomialPoleBound

end

end OAI
