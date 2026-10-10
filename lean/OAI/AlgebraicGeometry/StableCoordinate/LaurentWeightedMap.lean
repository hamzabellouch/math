import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic

namespace OAI

/-!
# Weighted polynomial evaluation in a Laurent polynomial algebra

The source convention has degree `T = -1`.  Consequently a variable of
integer weight `w i` is evaluated as a constant times `T (-w i)`.
This module supplies the graded compatibility needed when extending the
leading derivation to the source's Laurent localization.
-/

noncomputable section

namespace StableCoordinate.LaurentWeightedMap

open scoped LaurentPolynomial
open LaurentPolynomial

variable {k B σ : Type*} [CommRing k] [CommRing B] [Algebra k B]

/-- The polynomial map with prescribed homogeneous Laurent images. -/
def evaluate (w : σ → ℤ) (c : σ → B) : MvPolynomial σ k →ₐ[k] B[T;T⁻¹] :=
  MvPolynomial.aeval (fun i => C (c i) * T (-w i))

@[simp] theorem evaluate_X (w : σ → ℤ) (c : σ → B) (i : σ) :
    evaluate w c (MvPolynomial.X i : MvPolynomial σ k) = C (c i) * T (-w i) := by
  simp [evaluate]

/-- The exact Laurent exponent of an evaluated monomial. -/
theorem evaluate_monomial (w : σ → ℤ) (c : σ → B) (d : σ →₀ ℕ) (r : k) :
    evaluate w c (MvPolynomial.monomial d r) =
      C (MvPolynomial.aeval c (MvPolynomial.monomial d r)) * T (-Finsupp.weight w d) := by
  classical
  simp only [evaluate, MvPolynomial.aeval_monomial, LaurentPolynomial.algebraMap_apply]
  simp only [← single_eq_C_mul_T, AddMonoidAlgebra.single_pow, Finsupp.prod,
    AddMonoidAlgebra.prod_single]
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_neg_distrib, mul_assoc]

/-- Every polynomial homogeneous for the integer weights maps to a single
Laurent exponent.  The coefficient is its ordinary evaluation. -/
theorem evaluate_homogeneous (w : σ → ℤ) (c : σ → B)
    {p : MvPolynomial σ k} {m : ℤ} (hp : p.IsWeightedHomogeneous w m) :
    evaluate w c p = C (MvPolynomial.aeval c p) * T (-m) := by
  classical
  calc
    evaluate w c p = ∑ d ∈ p.support, evaluate w c (MvPolynomial.monomial d (p.coeff d)) := by
      conv_lhs => rw [p.as_sum, map_sum]
    _ = ∑ d ∈ p.support, C (MvPolynomial.aeval c (MvPolynomial.monomial d (p.coeff d))) * T (-m) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [evaluate_monomial, hp (MvPolynomial.mem_support_iff.mp hd)]
    _ = C (MvPolynomial.aeval c p) * T (-m) := by
      rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← p.as_sum]

/-- Coefficient-support formulation, used by Laurent derivation descent. -/
theorem coeff_evaluate_eq_zero (w : σ → ℤ) (c : σ → B)
    {p : MvPolynomial σ k} {m : ℤ} (hp : p.IsWeightedHomogeneous w m)
    (j : ℤ) (hj : j ≠ -m) :
    (evaluate w c p).coeff j = 0 := by
  rw [evaluate_homogeneous w c hp, ← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right (Ne.symm hj)]

/-- The graded compatibility is true for any polynomial map with these
generator images, not merely for the displayed evaluation map. -/
theorem map_homogeneous (w : σ → ℤ) (c : σ → B)
    (φ : MvPolynomial σ k →ₐ[k] B[T;T⁻¹])
    (hφ : ∀ i : σ, φ (MvPolynomial.X i) = C (c i) * T (-w i))
    {p : MvPolynomial σ k} {m : ℤ} (hp : p.IsWeightedHomogeneous w m) :
    φ p = C (MvPolynomial.aeval c p) * T (-m) := by
  have heq : φ = evaluate w c := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [hφ, evaluate_X]
  rw [heq]
  exact evaluate_homogeneous w c hp

end StableCoordinate.LaurentWeightedMap

end

end OAI
