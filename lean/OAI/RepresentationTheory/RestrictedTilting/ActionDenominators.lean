import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.LatticeGluing
import OAI.RepresentationTheory.RestrictedTilting.PolynomialActions

namespace OAI

/-! Polynomial action denominators over coordinates and fraction fields. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
open scoped BigOperators
open Matrix

section PolynomialDenominator
variable {k R K : Type*} [CommRing k] [CommRing R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K]

 
lemma polynomial_clear_denominator (p : Polynomial k) (b : R)
    (hb : algebraMap R K b ≠ 0) (d : ℕ) (hd : p.natDegree ≤ d) :
    ∃ a : R, algebraMap R K a =
      algebraMap R K b ^ d * Polynomial.aeval (-(algebraMap R K b)⁻¹) p := by
  refine ⟨∑ n ∈ Finset.range (d+1),
    algebraMap k R (p.coeff n) * (-1 : R)^n * b^(d-n), ?_⟩
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]
  simp only [map_sum, map_mul, map_pow, map_neg, map_one,
    ← IsScalarTower.algebraMap_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [pow_sub₀ _ hb (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  rw [neg_pow ((algebraMap R K b)⁻¹) n, inv_pow]
  simp only [Algebra.smul_def]
  ring

end PolynomialDenominator

variable {k ι : Type*} [Field k] [Infinite k] [Fintype ι] [DecidableEq ι]
variable (P : Matrix ι ι (Polynomial k))
    (h0 : polynomialMatrixEval P (0 : k) = 1)
    (hadd : ∀ s t : k, polynomialMatrixEval P (s+t) =
      polynomialMatrixEval P s * polynomialMatrixEval P t)

 
noncomputable def polynomialActionEquiv {K : Type*} [Field K] [Algebra k K] (t : K) :
    (ι → K) ≃ₗ[K] (ι → K) where
  toLinearMap := Matrix.toLin' (polynomialMatrixEval P t)
  invFun := Matrix.mulVec (polynomialMatrixEval P (-t))
  left_inv v := by
    change (polynomialMatrixEval P (-t)) *ᵥ ((polynomialMatrixEval P t) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← polynomialMatrixEval_add P hadd, neg_add_cancel,
      polynomialMatrixEval_zero P h0, Matrix.one_mulVec]
  right_inv v := by
    change (polynomialMatrixEval P t) *ᵥ ((polynomialMatrixEval P (-t)) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← polynomialMatrixEval_add P hadd, add_neg_cancel,
      polynomialMatrixEval_zero P h0, Matrix.one_mulVec]

variable {R K : Type*} [CommRing R] [Field K] [Algebra k R] [Algebra R K]
    [Algebra k K] [IsScalarTower k R K]

 

theorem polynomialAction_denominator (b : R) (hb : algebraMap R K b ≠ 0)
    (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    ∀ v ∈ coordinateLattice (R := R) (K := K) (ι := ι),
      b^d • polynomialActionEquiv P h0 hadd (-(algebraMap R K b)⁻¹) v ∈
      coordinateLattice (R := R) (K := K) (ι := ι) := by
  intro v hv
  apply (mem_coordinateLattice _).mpr
  intro i
  choose w hw using (mem_coordinateLattice v).mp hv
  choose a ha using fun j => polynomial_clear_denominator (P i j) b hb d (hd i j)
  refine ⟨∑ j, a j * w j, ?_⟩
  change algebraMap R K (∑ j, a j * w j) =
    b^d • ((Matrix.toLin' (polynomialMatrixEval P (-(algebraMap R K b)⁻¹))) v) i
  rw [Algebra.smul_def]
  rw [Matrix.toLin'_apply]
  simp only [map_sum, map_mul, ha, hw, map_pow, Matrix.mulVec, dotProduct,
    polynomialMatrixEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end

open scoped BigOperators
open Matrix

section FractionDenominator
variable {k R K : Type*} [CommRing k] [CommRing R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K]

lemma polynomial_clear_fraction_denominator (p : Polynomial k) (a b : R)
    (hb : algebraMap R K b ≠ 0) (d : ℕ) (hd : p.natDegree ≤ d) :
    ∃ c : R, algebraMap R K c =
      algebraMap R K b ^ d * Polynomial.aeval
        (algebraMap R K a * (algebraMap R K b)⁻¹) p := by
  refine ⟨∑ n ∈ Finset.range (d+1),
    algebraMap k R (p.coeff n) * a^n * b^(d-n), ?_⟩
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]
  simp only [map_sum, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [pow_sub₀ _ hb (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)), mul_pow, inv_pow]
  simp only [Algebra.smul_def]
  ring

end FractionDenominator

variable {k ι : Type*} [Field k] [Infinite k] [Fintype ι] [DecidableEq ι]
variable (P : Matrix ι ι (Polynomial k))
    (h0 : polynomialMatrixEval P (0 : k) = 1)
    (hadd : ∀ s t : k, polynomialMatrixEval P (s+t) =
      polynomialMatrixEval P s * polynomialMatrixEval P t)
variable {R K : Type*} [CommRing R] [Field K] [Algebra k R] [Algebra R K]
    [Algebra k K] [IsScalarTower k R K]

lemma polynomialActionEquiv_symm (t : K) :
    (polynomialActionEquiv P h0 hadd t).symm = polynomialActionEquiv P h0 hadd (-t) := by
  ext v i
  rfl

theorem polynomialAction_fraction_denominator (a b : R) (hb : algebraMap R K b ≠ 0)
    (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    ∀ v ∈ coordinateLattice (R := R) (K := K) (ι := ι),
      b^d • polynomialActionEquiv P h0 hadd
        (algebraMap R K a * (algebraMap R K b)⁻¹) v ∈
      coordinateLattice (R := R) (K := K) (ι := ι) := by
  intro v hv
  apply (mem_coordinateLattice _).mpr
  intro i
  choose w hw using (mem_coordinateLattice v).mp hv
  choose c hc using fun j => polynomial_clear_fraction_denominator (P i j) a b hb d (hd i j)
  refine ⟨∑ j, c j * w j, ?_⟩
  change algebraMap R K (∑ j, c j * w j) =
    b^d • ((Matrix.toLin' (polynomialMatrixEval P
      (algebraMap R K a * (algebraMap R K b)⁻¹))) v) i
  rw [Algebra.smul_def, Matrix.toLin'_apply]
  simp only [map_sum, map_mul, hc, hw, map_pow, Matrix.mulVec, dotProduct,
    polynomialMatrixEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end FiberFunctorProof

end

end OAI
