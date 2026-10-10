import Mathlib

namespace OAI

noncomputable section

namespace Problem335

open MvPolynomial

variable {K σ : Type*} [CommSemiring K]

/-- Repeated partial differentiation acts by a falling factorial on each monomial. -/
theorem iterate_pderiv_monomial (i : σ) (r : ℕ) (d : σ →₀ ℕ) (a : K) :
    (pderiv i)^[r] (monomial d a) =
      monomial (d - Finsupp.single i r) (a * (d i).descFactorial r) := by
  classical
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, pderiv_monomial,
      Nat.descFactorial_succ]
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.cast_mul]
    rw [show d - Finsupp.single i r - Finsupp.single i 1 =
      d - Finsupp.single i (r + 1) by rw [tsub_tsub, Finsupp.single_add]]
    congr 1
    ring

/-- Derivatives beyond a monomial's exponent vanish, in any characteristic. -/
theorem iterate_pderiv_monomial_eq_zero (i : σ) (r : ℕ) (d : σ →₀ ℕ)
    (a : K) (h : d i < r) :
    (pderiv i)^[r] (monomial d a) = 0 := by
  rw [iterate_pderiv_monomial, Nat.descFactorial_eq_zero_iff_lt.mpr h]
  simp

/-- Coefficients of a repeated derivative are shifted coefficients times a rising factorial. -/
theorem coeff_iterate_pderiv (i : σ) (r : ℕ) (p : MvPolynomial σ K)
    (m : σ →₀ ℕ) :
    ((pderiv i)^[r] p).coeff m =
      p.coeff (m + Finsupp.single i r) * (m i + 1).ascFactorial r := by
  classical
  induction r generalizing p with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih, coeff_pderiv, Nat.ascFactorial_succ]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_mul]
    rw [show m + Finsupp.single i r + Finsupp.single i 1 =
      m + Finsupp.single i (r + 1) by rw [add_assoc, ← Finsupp.single_add]]
    push_cast
    ring

end Problem335

end

end OAI
