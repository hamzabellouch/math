import OAI.AlgebraicGeometry.StableCoordinate.FactorialClosure
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Nat.Choose.Cast

namespace OAI

/-!
# Polynomial exponentials of locally nilpotent derivations

The exponential of a locally nilpotent derivation in characteristic zero is
an actual polynomial algebra homomorphism, not a formal power series.  This
is the forward algebraic interface for the additive-action step in Section 4.
-/

noncomputable section

namespace StableCoordinate.LNDExponential

open Function Polynomial Finset

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- The factorially divided `n`th iterate of a derivation. -/
def dividedIterate (D : Derivation k A A) (a : A) (n : ℕ) : A :=
  ((n.factorial : k)⁻¹) • (D : A → A)^[n] a

lemma dividedIterate_finiteSupport (D : Derivation k A A)
    (hD : IsLocallyNilpotent D) (a : A) :
    (Function.support (dividedIterate D a)).Finite := by
  obtain ⟨N, hN⟩ := hD a
  apply (Set.finite_Iio N).subset
  intro n hn
  by_contra h
  have hz := derivation_iterate_eq_zero_of_le D hN (Nat.le_of_not_gt h)
  exact hn (by simp [dividedIterate, hz])

/-- A finite-support construction of `exp(T D)(a)`. -/
def polynomial (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a : A) : A[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Finsupp.ofSupportFinite (dividedIterate D a) (dividedIterate_finiteSupport D hD a)))

@[simp]
lemma coeff_polynomial (D : Derivation k A A) (hD : IsLocallyNilpotent D)
    (a : A) (n : ℕ) :
    (polynomial D hD a).coeff n = ((n.factorial : k)⁻¹) • (D : A → A)^[n] a := rfl

lemma iterate_add (D : Derivation k A A) (n : ℕ) (a b : A) :
    (D : A → A)^[n] (a + b) = (D : A → A)^[n] a + (D : A → A)^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

lemma iterate_smul (D : Derivation k A A) (n : ℕ) (c : k) (a : A) :
    (D : A → A)^[n] (c • a) = c • (D : A → A)^[n] a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, Derivation.map_smul]

lemma polynomial_add (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a b : A) :
    polynomial D hD (a + b) = polynomial D hD a + polynomial D hD b := by
  ext n
  simp [smul_add]

lemma polynomial_smul (D : Derivation k A A) (hD : IsLocallyNilpotent D)
    (c : k) (a : A) : polynomial D hD (c • a) = c • polynomial D hD a := by
  ext n
  rw [coeff_polynomial, Polynomial.coeff_smul, coeff_polynomial, iterate_smul, smul_comm]

lemma polynomial_one (D : Derivation k A A) (hD : IsLocallyNilpotent D) :
    polynomial D hD 1 = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    have hzero : (D : A → A)^[n + 1] 1 = 0 :=
      derivation_iterate_eq_zero_of_le D (m := 1) (by simp) (by omega)
    simp [hzero, Polynomial.coeff_one]

variable [CharZero k]

lemma inverse_factorial_mul_choose (i j : ℕ) :
    ((i + j).factorial : k)⁻¹ * ((i + j).choose i : k) =
      (i.factorial : k)⁻¹ * (j.factorial : k)⁻¹ := by
  rw [Nat.cast_add_choose]
  have hi : (i.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hj : (j.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hij : ((i+j).factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

lemma dividedIterate_mul (D : Derivation k A A) (n : ℕ) (a b : A) :
    ((n.factorial : k)⁻¹) • (D : A → A)^[n] (a * b) =
    ∑ ij ∈ antidiagonal n,
      (((ij.1.factorial : k)⁻¹) • (D : A → A)^[ij.1] a) *
      (((ij.2.factorial : k)⁻¹) • (D : A → A)^[ij.2] b) := by
  rw [derivation_iterate_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  have hn : i + j = n := Finset.mem_antidiagonal.mp hij
  subst n
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inverse_factorial_mul_choose]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm ((i.factorial : k)⁻¹)]

lemma polynomial_mul (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a b : A) :
    polynomial D hD (a * b) = polynomial D hD a * polynomial D hD b := by
  ext n
  simpa only [coeff_polynomial, Polynomial.coeff_mul] using dividedIterate_mul D n a b

/-- The polynomial exponential is a coefficient-field algebra homomorphism. -/
def exponential (D : Derivation k A A) (hD : IsLocallyNilpotent D) : A →ₐ[k] A[X] where
  toFun := polynomial D hD
  map_one' := polynomial_one D hD
  map_mul' := polynomial_mul D hD
  map_zero' := by
    ext n
    simp [Function.iterate_fixed (map_zero D)]
  map_add' := polynomial_add D hD
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, polynomial_smul, polynomial_one]
    exact (Algebra.algebraMap_eq_smul_one c).symm

@[simp]
lemma coeff_exponential (D : Derivation k A A) (hD : IsLocallyNilpotent D)
    (a : A) (n : ℕ) :
    (exponential D hD a).coeff n = ((n.factorial : k)⁻¹) • (D : A → A)^[n] a :=
  coeff_polynomial D hD a n

@[simp]
lemma coeff_exponential_zero (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a : A) :
    (exponential D hD a).coeff 0 = a := by simp

@[simp]
lemma coeff_exponential_one (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a : A) :
    (exponential D hD a).coeff 1 = D a := by simp

end StableCoordinate.LNDExponential

end

end OAI
