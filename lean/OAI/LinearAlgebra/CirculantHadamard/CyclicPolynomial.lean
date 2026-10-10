import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot

namespace OAI

universe uR uA

/-!
# The polynomial presentation of the actual cyclic group algebra

For a commutative coefficient ring and a positive integer `n`, the cyclic group
algebra is the quotient of `R[X]` by `X ^ n - 1`. The two maps are defined
by their universal properties, and both inverse identities are proved explicitly.
No domain property of the finite group algebra is used.
-/

noncomputable section

namespace CirculantHadamard.CyclicPolynomial

open Polynomial

variable (R : Type uR) [CommRing R] (n : ℕ)

/-- The defining polynomial of the cyclic group algebra. -/
def relation : R[X] := X ^ n - 1

/-- The basis element at the distinguished generator of the cyclic group. -/
def generator : AddMonoidAlgebra R (ZMod n) := AddMonoidAlgebra.single 1 1

theorem generator_pow : generator R n ^ n = 1 := by
  simp [generator, AddMonoidAlgebra.single_pow, nsmul_eq_mul,
    AddMonoidAlgebra.one_def]

theorem root_pow : AdjoinRoot.root (relation R n) ^ n = 1 := by
  have h : AdjoinRoot.mk (relation R n) (X ^ n - 1) = 0 :=
    AdjoinRoot.mk_self (f := relation R n)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact sub_eq_zero.mp h

variable {R}

/-- A genuine cyclic character associated to an element whose `n`th power is one. -/
def powerCharacter {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) : Multiplicative (ZMod n) →* A where
  toFun a := x ^ a.toAdd.val
  map_one' := by
    change x ^ (0 : ZMod n).val = 1
    simp
  map_mul' a b := by
    change x ^ (a.toAdd + b.toAdd).val =
      x ^ a.toAdd.val * x ^ b.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

@[simp]
theorem powerCharacter_apply {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) (i : ZMod n) :
    powerCharacter n x hx (Multiplicative.ofAdd i) = x ^ i.val := rfl

@[simp]
theorem powerCharacter_generator {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) :
    powerCharacter n x hx (Multiplicative.ofAdd 1) = x := by
  change x ^ (1 : ZMod n).val = x
  rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hx, pow_one]

variable (R)

/-- Send the cyclic basis element at `i` to the `i.val`th power of the root. -/
def toPolynomial [NeZero n] :
    AddMonoidAlgebra R (ZMod n) →ₐ[R] AdjoinRoot (relation R n) :=
  AddMonoidAlgebra.lift R (AdjoinRoot (relation R n)) (ZMod n)
    (powerCharacter n (AdjoinRoot.root (relation R n)) (root_pow R n))

@[simp]
theorem toPolynomial_single [NeZero n] (i : ZMod n) (r : R) :
    toPolynomial R n (AddMonoidAlgebra.single i r) =
      algebraMap R (AdjoinRoot (relation R n)) r *
        AdjoinRoot.root (relation R n) ^ i.val := by
  simp [toPolynomial, Algebra.smul_def]

@[simp]
theorem toPolynomial_generator [NeZero n] :
    toPolynomial R n (generator R n) = AdjoinRoot.root (relation R n) := by
  simp only [generator, toPolynomial, AddMonoidAlgebra.lift_single,
    powerCharacter_generator, one_smul]

theorem generator_isRoot : aeval (generator R n) (relation R n) = 0 := by
  simp [relation, generator_pow]

/-- Evaluate the polynomial quotient at the actual cyclic group-ring generator. -/
def fromPolynomial :
    AdjoinRoot (relation R n) →ₐ[R] AddMonoidAlgebra R (ZMod n) :=
  AdjoinRoot.liftAlgHom (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n)

@[simp]
theorem fromPolynomial_root :
    fromPolynomial R n (AdjoinRoot.root (relation R n)) = generator R n := by
  exact AdjoinRoot.liftAlgHom_root (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n)

@[simp]
theorem fromPolynomial_mk (p : R[X]) :
    fromPolynomial R n (AdjoinRoot.mk (relation R n) p) =
      aeval (generator R n) p := by
  exact AdjoinRoot.liftAlgHom_mk (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n) p

theorem generator_pow_val [NeZero n] (i : ZMod n) :
    generator R n ^ i.val = AddMonoidAlgebra.single i 1 := by
  simp [generator, AddMonoidAlgebra.single_pow, nsmul_eq_mul]

theorem toPolynomial_comp_fromPolynomial [NeZero n] :
    (toPolynomial R n).comp (fromPolynomial R n) =
      AlgHom.id R (AdjoinRoot (relation R n)) := by
  apply AdjoinRoot.algHom_ext
  simp

theorem fromPolynomial_comp_toPolynomial [NeZero n] :
    (fromPolynomial R n).comp (toPolynomial R n) =
      AlgHom.id R (AddMonoidAlgebra R (ZMod n)) := by
  apply AddMonoidAlgebra.algHom_ext
  · intro i
    simp [generator_pow_val]
  · exact Subsingleton.elim _ _

/-- The actual cyclic group algebra is the polynomial quotient by `X ^ n - 1`. -/
def cyclicEquiv [NeZero n] :
    AddMonoidAlgebra R (ZMod n) ≃ₐ[R] AdjoinRoot (relation R n) :=
  AlgEquiv.ofAlgHom (toPolynomial R n) (fromPolynomial R n)
    (toPolynomial_comp_fromPolynomial R n) (fromPolynomial_comp_toPolynomial R n)

@[simp]
theorem cyclicEquiv_single [NeZero n] (i : ZMod n) (r : R) :
    cyclicEquiv R n (AddMonoidAlgebra.single i r) =
      algebraMap R (AdjoinRoot (relation R n)) r *
        AdjoinRoot.root (relation R n) ^ i.val :=
  toPolynomial_single R n i r

@[simp]
theorem cyclicEquiv_generator [NeZero n] :
    cyclicEquiv R n (generator R n) = AdjoinRoot.root (relation R n) :=
  toPolynomial_generator R n

@[simp]
theorem cyclicEquiv_symm_root [NeZero n] :
    (cyclicEquiv R n).symm (AdjoinRoot.root (relation R n)) = generator R n :=
  fromPolynomial_root R n

@[simp]
theorem cyclicEquiv_symm_mk [NeZero n] (p : R[X]) :
    (cyclicEquiv R n).symm (AdjoinRoot.mk (relation R n) p) =
      aeval (generator R n) p :=
  fromPolynomial_mk R n p

@[simp]
theorem cyclicEquiv_aeval [NeZero n] (p : R[X]) :
    cyclicEquiv R n (aeval (generator R n) p) =
      AdjoinRoot.mk (relation R n) p := by
  rw [← Polynomial.aeval_algHom_apply, cyclicEquiv_generator,
    AdjoinRoot.aeval_eq]

end CirculantHadamard.CyclicPolynomial

end

end OAI
