import OAI.AlgebraicGeometry.StableCoordinate.FactorialClosure
import Mathlib.Algebra.Polynomial.Laurent

namespace OAI

/-!
# Homogeneous locally nilpotent derivations on a Laurent polynomial ring

The degree convention in the manuscript is `deg τ = -1`. Thus a derivation
of degree `m` maps constants to Laurent monomials with exponent `-m`.
We use the exponent `q` directly, so the source application takes `q = -m`.
-/

noncomputable section

namespace StableCoordinate.LaurentDescent

open LaurentPolynomial Function
open scoped LaurentPolynomial

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

@[simp]
theorem coeff_C_mul_T (a : A) (q i : ℤ) :
    (C a * T q : A[T;T⁻¹]).coeff i = if q = i then a else 0 := by
  rw [← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Vanishing of a derivation on `T` implies vanishing on every integral power. -/
theorem derivation_T_eq_zero (D : Derivation k A[T;T⁻¹] A[T;T⁻¹])
    (hT : D (T 1) = 0) (n : ℤ) : D (T n) = 0 := by
  have hneg : D (T (-1)) = 0 := by
    simpa [hT] using D.leibniz_invOf (T 1)
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [T_add, D.leibniz, hT, ih]
    simp
  | pred n ih =>
    rw [sub_eq_add_neg, T_add, D.leibniz, hneg, ih]
    simp

/-- Constants followed by a specified coefficient of the derivation. -/
def coefficientLinear (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ) : A →ₗ[k] A where
  toFun a := (D (C a)).coeff q
  map_add' a b := by simp
  map_smul' r a := by
    change (D ((IsScalarTower.toAlgHom k A A[T;T⁻¹]) (r • a))).coeff q = _
    rw [map_smul, Derivation.map_smul]
    rfl

/-- The precise homogeneous-on-constants condition needed for Laurent descent. -/
def HomogeneousOnConstants (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ) : Prop :=
  ∀ a : A, D (C a) = C ((D (C a)).coeff q) * T q

/-- The homogeneous-on-constants condition is exactly absence of all other exponents. -/
theorem homogeneousOnConstants_iff (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ) :
    HomogeneousOnConstants D q ↔
      ∀ (a : A) (i : ℤ), i ≠ q → (D (C a)).coeff i = 0 := by
  constructor
  · intro h a i hi
    rw [h a, coeff_C_mul_T, ite_eq_right (Ne.symm hi)]
  · intro h a
    apply LaurentPolynomial.ext
    intro i
    by_cases hi : i = q
    · subst i
      simp
    · rw [h a i hi, coeff_C_mul_T, ite_eq_right (Ne.symm hi)]

/-- The coefficient derivation obtained from a homogeneous Laurent derivation. -/
def descend (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ)
    (hq : HomogeneousOnConstants D q) : Derivation k A A where
  toLinearMap := coefficientLinear D q
  map_one_eq_zero' := by simp [coefficientLinear]
  leibniz' a b := by
    change (D (C (a * b))).coeff q =
      a • (D (C b)).coeff q + b • (D (C a)).coeff q
    rw [map_mul, D.leibniz, smul_eq_mul, smul_eq_mul, hq a, hq b]
    have hmul (r s : A) : C r * (C s * T q : A[T;T⁻¹]) = C (r * s) * T q := by
      rw [map_mul, mul_assoc]
    simp only [hmul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul_T,
      ite_true, smul_eq_mul]

@[simp]
theorem descend_apply (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ)
    (hq : HomogeneousOnConstants D q) (a : A) :
    descend D q hq a = (D (C a)).coeff q := rfl

/-- The defining homogeneous expression in terms of the descended derivation. -/
theorem derivation_C_eq (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ)
    (hq : HomogeneousOnConstants D q) (a : A) :
    D (C a) = C (descend D q hq a) * T q := hq a

/-- A homogeneous Laurent derivation differentiates a monomial only through its coefficient. -/
theorem derivation_C_mul_T (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ)
    (hq : HomogeneousOnConstants D q) (hT : D (T 1) = 0) (a : A) (j : ℤ) :
    D (C a * T j) = C (descend D q hq a) * T (q + j) := by
  rw [D.leibniz, derivation_T_eq_zero D hT, smul_zero, zero_add, smul_eq_mul,
    derivation_C_eq D q hq, mul_comm (T j), mul_T_assoc]

/-- The exact iterate formula; in the source `q=-m`. -/
theorem iterate_C (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ)
    (hq : HomogeneousOnConstants D q) (hT : D (T 1) = 0) (a : A) (n : ℕ) :
    (D : A[T;T⁻¹] → A[T;T⁻¹])^[n] (C a) =
      C ((descend D q hq : A → A)^[n] a) * T ((n : ℤ) * q) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, derivation_C_mul_T D q hq hT,
      Function.iterate_succ_apply']
    congr 2
    push_cast
    ring

/-- Local nilpotence descends from the Laurent ring to the coefficient ring. -/
theorem descend_locallyNilpotent (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ)
    (hq : HomogeneousOnConstants D q) (hT : D (T 1) = 0)
    (hD : StableCoordinate.IsLocallyNilpotent D) :
    StableCoordinate.IsLocallyNilpotent (descend D q hq) := by
  intro a
  obtain ⟨n, hn⟩ := hD (C a)
  refine ⟨n, ?_⟩
  rw [iterate_C D q hq hT] at hn
  have hc := congrArg (fun p : A[T;T⁻¹] => p.coeff ((n : ℤ) * q)) hn
  simpa using hc

/-- A derivation on the Laurent ring is determined by constants and `T`. -/
theorem derivation_eq_zero_of_constants (D : Derivation k A[T;T⁻¹] A[T;T⁻¹])
    (hC : ∀ a : A, D (C a) = 0) (hT : D (T 1) = 0) : D = 0 := by
  apply Derivation.ext
  intro p
  change D p = 0
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => simp [map_add, hp, hp']
  | C_mul_T n a => simp [D.leibniz, hC, derivation_T_eq_zero D hT]

/-- Nonzero homogeneous Laurent derivations descend to nonzero derivations. -/
theorem descend_ne_zero (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ)
    (hq : HomogeneousOnConstants D q) (hT : D (T 1) = 0) (hD : D ≠ 0) :
    descend D q hq ≠ 0 := by
  intro hE
  apply hD
  apply derivation_eq_zero_of_constants D ?_ hT
  intro a
  rw [derivation_C_eq D q hq, hE]
  simp

/-- An invariant Laurent monomial has invariant coefficient after descent. -/
theorem descend_invariant (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ)
    (hq : HomogeneousOnConstants D q) (hT : D (T 1) = 0) {a : A} {j : ℤ}
    (ha : D (C a * T j) = 0) : descend D q hq a = 0 := by
  rw [derivation_C_mul_T D q hq hT] at ha
  have hc := congrArg (fun p : A[T;T⁻¹] => p.coeff (q + j)) ha
  simpa using hc

/-- The standalone Laurent descent package used in `gr:descent`. -/
theorem exists_descended_lnd (D : Derivation k A[T;T⁻¹] A[T;T⁻¹]) (q : ℤ)
    (hq : HomogeneousOnConstants D q) (hT : D (T 1) = 0)
    (hD : StableCoordinate.IsLocallyNilpotent D) (hne : D ≠ 0) :
    ∃ E : Derivation k A A,
      StableCoordinate.IsLocallyNilpotent E ∧ E ≠ 0 ∧
      (∀ a : A, D (C a) = C (E a) * T q) ∧
      (∀ (a : A) (j : ℤ), D (C a * T j) = 0 → E a = 0) := by
  refine ⟨descend D q hq, descend_locallyNilpotent D q hq hT hD,
    descend_ne_zero D q hq hT hne, derivation_C_eq D q hq, ?_⟩
  intro a j ha
  exact descend_invariant D q hq hT ha

end StableCoordinate.LaurentDescent

end

end OAI
