import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Differentiating polynomial additive actions

This file supplies the algebraic additive-action to locally nilpotent derivation
interface used when the line-bundle lift is restricted to its punctured total
space.  The action law is an equality of bivariate polynomials, not a merely
pointwise identity.  No reducedness or characteristic-zero hypothesis is needed
for the forward implication.
-/

noncomputable section

namespace StableCoordinate.CoactionLND

open Polynomial

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]

/-- A polynomial additive-group action on an affine algebra, in contravariant
form. In `coassoc`, the outer polynomial variable is the second parameter and
the inner variable is the first parameter. -/
structure PolynomialAdditiveAction where
  toAlgHom : A →ₐ[k] A[X]
  identity : ∀ a, (toAlgHom a).coeff 0 = a
  coassoc : ∀ a,
    (toAlgHom a).map toAlgHom.toRingHom =
      taylor (X : A[X]) ((toAlgHom a).map (C : A →+* A[X]))

variable {k A}

/-- Hasse derivatives commute with coefficient homomorphisms. -/
lemma hasseDeriv_map {B : Type*} [CommRing B] (f : A →+* B)
    (p : A[X]) (n : ℕ) :
    hasseDeriv n (p.map f) = (hasseDeriv n p).map f := by
  ext j
  simp only [hasseDeriv_coeff, coeff_map, map_mul, map_natCast]

/-- Reading the outer coefficient of the universal translate gives a Hasse
 derivative in the inner variable. -/
lemma coeff_universal_translate (p : A[X]) (n : ℕ) :
    (taylor (X : A[X]) (p.map (C : A →+* A[X]))).coeff n =
      hasseDeriv n p := by
  rw [taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X]

namespace PolynomialAdditiveAction

variable (α : PolynomialAdditiveAction k A)

/-- The coefficient of the action parameter is its infinitesimal derivation. -/
def derivation : Derivation k A A where
  toFun a := (α.toAlgHom a).coeff 1
  map_add' a b := by simp
  map_smul' r a := by simp
  map_one_eq_zero' := by simp [coeff_one]
  leibniz' a b := by
    change (α.toAlgHom (a * b)).coeff 1 = a • (α.toAlgHom b).coeff 1 + b • (α.toAlgHom a).coeff 1
    simp only [map_mul, mul_coeff_one, α.identity, smul_eq_mul]
    ring

@[simp] theorem derivation_apply (a : A) :
    α.derivation a = (α.toAlgHom a).coeff 1 := rfl

/-- Coassociativity written coefficientwise. -/
theorem action_coeff (a : A) (n : ℕ) :
    α.toAlgHom ((α.toAlgHom a).coeff n) = hasseDeriv n (α.toAlgHom a) := by
  simpa only [coeff_map, coeff_universal_translate, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
    congrArg (fun p : A[X][X] => p.coeff n) (α.coassoc a)

/-- The infinitesimal action advances action coefficients by one index. -/
theorem derivation_coeff (a : A) (n : ℕ) :
    α.derivation ((α.toAlgHom a).coeff n) =
      (n + 1) • (α.toAlgHom a).coeff (n + 1) := by
  rw [derivation_apply, α.action_coeff, hasseDeriv_coeff]
  simp [Nat.add_comm, Nat.choose_succ_self_right, nsmul_eq_mul]

/-- The iterates are factorial multiples of action coefficients. -/
theorem iterate_derivation (a : A) (n : ℕ) :
    (α.derivation : A → A)^[n] a = n.factorial • (α.toAlgHom a).coeff n := by
  induction n with
  | zero => simp [α.identity]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_nsmul, α.derivation_coeff,
      smul_smul, Nat.factorial_succ]
    rw [Nat.mul_comm]

/-- An algebraic additive action differentiates to a locally nilpotent
 derivation; its action polynomial gives an explicit nilpotence bound. -/
theorem iterate_derivation_eq_zero (a : A) :
    (α.derivation : A → A)^[(α.toAlgHom a).natDegree + 1] a = 0 := by
  rw [α.iterate_derivation, coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _),
    smul_zero]

/-- Pointwise local nilpotence in the common interface used by the project. -/
theorem locallyNilpotent : ∀ a, ∃ n : ℕ, (α.derivation : A → A)^[n] a = 0 :=
  fun a => ⟨_, α.iterate_derivation_eq_zero a⟩

/-- In characteristic zero over a domain, a vanishing infinitesimal action
 forces the entire polynomial action to be trivial. -/
theorem action_eq_C_of_derivation_eq_zero [NoZeroDivisors A] [CharZero A]
    (h : α.derivation = 0) (a : A) : α.toAlgHom a = C a := by
  ext n
  cases n with
  | zero => simp [α.identity]
  | succ n =>
    have hc := α.derivation_coeff a n
    rw [h, Derivation.zero_apply] at hc
    have hn : (n + 1 : A) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hz : (α.toAlgHom a).coeff (n + 1) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hn
      simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using hc.symm
    simpa using hz

/-- A nontrivial polynomial additive action has a nonzero infinitesimal
 derivation in characteristic zero over a domain. -/
theorem derivation_ne_zero_of_nontrivial [NoZeroDivisors A] [CharZero A]
    (h : ∃ a, α.toAlgHom a ≠ C a) : α.derivation ≠ 0 := by
  intro hzero
  obtain ⟨a, ha⟩ := h
  exact ha (α.action_eq_C_of_derivation_eq_zero hzero a)

/-- Equivariance of additive actions differentiates to equivariance of their
 derivations.  In particular, a lifted action differentiates to an extension
 of the original derivation. -/
theorem derivation_naturality {B : Type*} [CommRing B] [Algebra k B]
    (β : PolynomialAdditiveAction k B) (f : A →ₐ[k] B)
    (hf : ∀ a, β.toAlgHom (f a) = (α.toAlgHom a).map f.toRingHom) (a : A) :
    β.derivation (f a) = f (α.derivation a) := by
  simp only [derivation_apply, hf, coeff_map, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom]

/-- An injective equivariant algebra extension preserves nontriviality of the
 infinitesimal derivation. -/
theorem derivation_ne_zero_of_injective {B : Type*} [CommRing B] [Algebra k B]
    (β : PolynomialAdditiveAction k B) (f : A →ₐ[k] B)
    (hf : ∀ a, β.toAlgHom (f a) = (α.toAlgHom a).map f.toRingHom)
    (hinj : Function.Injective f) (hα : α.derivation ≠ 0) : β.derivation ≠ 0 := by
  intro hβ
  apply hα
  ext a
  apply hinj
  have h := α.derivation_naturality β f hf a
  rw [hβ, Derivation.zero_apply] at h
  simpa using h.symm

end PolynomialAdditiveAction

end StableCoordinate.CoactionLND

end

end OAI
