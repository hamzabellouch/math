import OAI.AlgebraicGeometry.StableCoordinate.FilteredRees
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Tactic.Abel

namespace OAI

/-!
# A shifted derivation on the extended Rees algebra

A derivation with filtration shift `m` acts coefficientwise on Laurent
polynomials and is multiplied by `T^m`.  It preserves the Rees algebra,
annihilates its parameter, and hence descends to the associated graded ring.
-/

namespace StableCoordinate.FilteredRees

open AddMonoidAlgebra

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Coefficientwise application of a linear map to Laurent polynomials. -/
noncomputable def coefficientLinear (f : A →ₗ[k] A) :
    LaurentPolynomial A →ₗ[k] LaurentPolynomial A :=
  (AddMonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap f).comp
      (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap)

@[simp] theorem coefficientLinear_coeff (f : A →ₗ[k] A)
    (p : LaurentPolynomial A) (d : ℤ) :
    (coefficientLinear f p).coeff d = f (p.coeff d) := rfl

@[simp] theorem coefficientLinear_single (f : A →ₗ[k] A) (d : ℤ) (a : A) :
    coefficientLinear f (single d a) = single d (f a) := by
  ext i
  rw [coefficientLinear_coeff]
  simp only [coeff_single, Finsupp.single_apply]
  split_ifs <;> simp only [map_zero]

private theorem coefficientLinear_leibniz (D : Derivation k A A)
    (p q : LaurentPolynomial A) :
    coefficientLinear D.toLinearMap (p * q) =
      p * coefficientLinear D.toLinearMap q + q * coefficientLinear D.toLinearMap p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp only [zero_mul, map_zero, mul_zero, add_zero]
  | add p₁ p₂ ih₁ ih₂ =>
      simp only [add_mul, map_add, ih₁, ih₂, mul_add]
      abel
  | single i a =>
      induction q using AddMonoidAlgebra.induction_linear with
      | zero => simp only [zero_mul, map_zero, mul_zero, add_zero]
      | add q₁ q₂ ih₁ ih₂ =>
          simp only [mul_add, map_add, ih₁, ih₂, add_mul]
          abel
      | single j b =>
          simp only [single_mul_single, coefficientLinear_single]
          change single (i + j) (D (a * b)) =
            single (i + j) (a * D b) + single (j + i) (b * D a)
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, single_add]
          rw [add_comm j i]

/-- Coefficientwise extension of a derivation, fixing the Laurent parameter. -/
noncomputable def coefficientDerivation (D : Derivation k A A) :
    Derivation k (LaurentPolynomial A) (LaurentPolynomial A) :=
  Derivation.mk' (coefficientLinear D.toLinearMap) (by
    intro p q
    exact coefficientLinear_leibniz D p q)

@[simp] theorem coefficientDerivation_coeff (D : Derivation k A A)
    (p : LaurentPolynomial A) (d : ℤ) :
    (coefficientDerivation D p).coeff d = D (p.coeff d) := rfl

@[simp] theorem coefficientDerivation_single (D : Derivation k A A)
    (d : ℤ) (a : A) :
    coefficientDerivation D (single d a) = single d (D a) :=
  coefficientLinear_single D.toLinearMap d a

/-- Multiplication by a Laurent monomial changes the filtration shift. -/
noncomputable def shiftedDerivation (D : Derivation k A A) (m : ℤ) :
    Derivation k (LaurentPolynomial A) (LaurentPolynomial A) :=
  (single m (1 : A) : LaurentPolynomial A) • coefficientDerivation D

@[simp] theorem shiftedDerivation_coeff (D : Derivation k A A) (m : ℤ)
    (p : LaurentPolynomial A) (d : ℤ) :
    (shiftedDerivation D m p).coeff d = D (p.coeff (d - m)) := by
  change (single m 1 * coefficientDerivation D p).coeff d = _
  rw [coeff_single_mul_apply, one_mul, coefficientDerivation_coeff]
  congr 2
  omega

@[simp] theorem shiftedDerivation_single (D : Derivation k A A) (m d : ℤ) (a : A) :
    shiftedDerivation D m (single d a) = single (d + m) (D a) := by
  change single m 1 * coefficientDerivation D (single d a) = _
  rw [coefficientDerivation_single, single_mul_single, one_mul, add_comm]


/-- Iterating the shifted Laurent derivation on a monomial does not introduce
any additional coefficient factors. -/
theorem shiftedDerivation_iterate_single (D : Derivation k A A)
    (m d : ℤ) (a : A) (n : ℕ) :
    ((shiftedDerivation D m : LaurentPolynomial A → LaurentPolynomial A)^[n])
      (single d a) = single (d + (n : ℤ) * m) (((D : A → A)^[n]) a) := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, add_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, shiftedDerivation_single,
        Function.iterate_succ_apply']
      congr 1
      push_cast
      ring

/-- Local nilpotence extends to Laurent polynomials after any integer shift. -/
theorem shiftedDerivation_locallyNilpotent (D : Derivation k A A) (m : ℤ)
    (hD : ∀ a, ∃ n, ((D : A → A)^[n]) a = 0) :
    ∀ p : LaurentPolynomial A,
      ∃ n, ((shiftedDerivation D m : LaurentPolynomial A → LaurentPolynomial A)^[n]) p = 0 := by
  intro p
  have hzero : ∀ n, ((shiftedDerivation D m : LaurentPolynomial A → LaurentPolynomial A)^[n]) 0 = 0 :=
    fun n => Function.iterate_fixed (map_zero (shiftedDerivation D m)) n
  have hadd : ∀ n (p q : LaurentPolynomial A),
      ((shiftedDerivation D m : LaurentPolynomial A → LaurentPolynomial A)^[n]) (p + q) =
      ((shiftedDerivation D m : LaurentPolynomial A → LaurentPolynomial A)^[n]) p +
      ((shiftedDerivation D m : LaurentPolynomial A → LaurentPolynomial A)^[n]) q := by
    intro n p q
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, rfl⟩
  | add p q hp hq =>
      obtain ⟨n, hn⟩ := hp
      obtain ⟨l, hl⟩ := hq
      refine ⟨n + l, ?_⟩
      rw [hadd]
      have hpn : ((shiftedDerivation D m : LaurentPolynomial A → LaurentPolynomial A)^[n+l]) p = 0 := by
        rw [Nat.add_comm, Function.iterate_add_apply, hn, hzero]
      have hql : ((shiftedDerivation D m : LaurentPolynomial A → LaurentPolynomial A)^[n+l]) q = 0 := by
        rw [Function.iterate_add_apply, hl, hzero]
      rw [hpn, hql, add_zero]
  | single d a =>
      obtain ⟨n, hn⟩ := hD a
      exact ⟨n, by rw [shiftedDerivation_iterate_single, hn, single_zero]⟩

variable (F : ℤ → Submodule k A) [SetLike.GradedMonoid F]
variable (D : Derivation k A A) (m : ℤ)
variable (hshift : ∀ d (a : A), a ∈ F d → D a ∈ F (d + m))

/-- Restriction of the shifted Laurent derivation to the Rees algebra. -/
noncomputable def reesDerivation : Derivation k (rees F) (rees F) where
  toFun p := ⟨shiftedDerivation D m p, by
    intro d
    rw [shiftedDerivation_coeff]
    simpa only [sub_add_cancel] using hshift (d - m) ((p : LaurentPolynomial A).coeff (d - m))
      (p.property (d - m))⟩
  map_add' p q := Subtype.ext ((shiftedDerivation D m).map_add p q)
  map_smul' c p := Subtype.ext ((shiftedDerivation D m).map_smul c p)
  map_one_eq_zero' := Subtype.ext (shiftedDerivation D m).map_one_eq_zero
  leibniz' p q := Subtype.ext ((shiftedDerivation D m).leibniz p q)

@[simp] theorem reesDerivation_coe (p : rees F) :
    (reesDerivation F D m hshift p : LaurentPolynomial A) = shiftedDerivation D m p := rfl

@[simp] theorem reesDerivation_parameter (hmono : Monotone F) :
    reesDerivation F D m hshift (parameter F hmono) = 0 := by
  apply Subtype.ext
  change shiftedDerivation D m (single 1 1) = 0
  rw [shiftedDerivation_single, Derivation.map_one_eq_zero, single_zero]

/-- The parameter ideal is invariant under the Rees derivation. -/
theorem reesDerivation_preserves_parameterIdeal (hmono : Monotone F)
    (p : rees F) (hp : p ∈ parameterIdeal F hmono) :
    reesDerivation F D m hshift p ∈ parameterIdeal F hmono := by
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
  rw [Derivation.leibniz, reesDerivation_parameter, smul_zero, add_zero]
  exact Ideal.mem_span_singleton.mpr ⟨reesDerivation F D m hshift q, rfl⟩

/-- The induced derivation on the genuine associated graded ring. -/
noncomputable def gradedDerivation (hmono : Monotone F) :
    Derivation k (Gr F hmono) (Gr F hmono) :=
  Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective k (parameterIdeal F hmono))
    (d := reesDerivation F D m hshift) (by
      intro p hp
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact reesDerivation_preserves_parameterIdeal F D m hshift hmono p
        (Ideal.Quotient.eq_zero_iff_mem.mp hp))


@[simp] theorem gradedDerivation_mk (hmono : Monotone F) (p : rees F) :
    gradedDerivation F D m hshift hmono (Ideal.Quotient.mk (parameterIdeal F hmono) p) =
      Ideal.Quotient.mk (parameterIdeal F hmono) (reesDerivation F D m hshift p) :=
  Derivation.liftOfSurjective_apply _ _ p

/-- Exact representative formula for the induced homogeneous derivation. -/
theorem gradedDerivation_initial (hmono : Monotone F) (d : ℤ) (a : F d) :
    gradedDerivation F D m hshift hmono (initial F hmono d a) =
      initial F hmono (d + m) ⟨D a, hshift d a a.property⟩ := by
  rw [initial, gradedDerivation_mk]
  congr 1
  apply Subtype.ext
  exact shiftedDerivation_single D m d a

theorem reesDerivation_iterate_coe (p : rees F) (n : ℕ) :
    (((reesDerivation F D m hshift : rees F → rees F)^[n]) p : LaurentPolynomial A) =
      ((shiftedDerivation D m : LaurentPolynomial A → LaurentPolynomial A)^[n]) p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', reesDerivation_coe, ih,
        Function.iterate_succ_apply']

theorem reesDerivation_locallyNilpotent
    (hD : ∀ a, ∃ n, ((D : A → A)^[n]) a = 0) :
    ∀ p : rees F, ∃ n, ((reesDerivation F D m hshift : rees F → rees F)^[n]) p = 0 := by
  intro p
  obtain ⟨n, hn⟩ := shiftedDerivation_locallyNilpotent D m hD (p : LaurentPolynomial A)
  refine ⟨n, Subtype.ext ?_⟩
  rw [reesDerivation_iterate_coe]
  exact hn

theorem gradedDerivation_iterate_mk (hmono : Monotone F) (p : rees F) (n : ℕ) :
    ((gradedDerivation F D m hshift hmono : Gr F hmono → Gr F hmono)^[n])
      (Ideal.Quotient.mk (parameterIdeal F hmono) p) =
    Ideal.Quotient.mk (parameterIdeal F hmono)
      (((reesDerivation F D m hshift : rees F → rees F)^[n]) p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, gradedDerivation_mk,
        Function.iterate_succ_apply']

/-- Local nilpotence passes to the actual associated graded ring. -/
theorem gradedDerivation_locallyNilpotent (hmono : Monotone F)
    (hD : ∀ a, ∃ n, ((D : A → A)^[n]) a = 0) :
    ∀ p : Gr F hmono,
      ∃ n, ((gradedDerivation F D m hshift hmono : Gr F hmono → Gr F hmono)^[n]) p = 0 := by
  intro p
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective p
  obtain ⟨n, hn⟩ := reesDerivation_locallyNilpotent F D m hshift hD q
  exact ⟨n, by rw [gradedDerivation_iterate_mk, hn, map_zero]⟩

/-- Attaining the filtration shift on one element forces a nonzero leading
associated-graded derivation. -/
theorem gradedDerivation_ne_zero (hmono : Monotone F) (d : ℤ) (a : F d)
    (hDa : D a ∉ F (d + m - 1)) :
    gradedDerivation F D m hshift hmono ≠ 0 := by
  intro hzero
  have hz := congrArg (fun E : Derivation k (Gr F hmono) (Gr F hmono) =>
    E (initial F hmono d a)) hzero
  rw [gradedDerivation_initial, Derivation.zero_apply] at hz
  exact hDa ((initial_eq_zero_iff F hmono (d + m) _).mp hz)

/-- Every invariant representative gives an invariant initial form. -/
theorem gradedDerivation_initial_eq_zero (hmono : Monotone F) (d : ℤ) (a : F d)
    (ha : D a = 0) :
    gradedDerivation F D m hshift hmono (initial F hmono d a) = 0 := by
  rw [gradedDerivation_initial, initial_eq_zero_iff]
  change D a ∈ F (d + m - 1)
  rw [ha]
  exact (F (d + m - 1)).zero_mem

end StableCoordinate.FilteredRees

end OAI
