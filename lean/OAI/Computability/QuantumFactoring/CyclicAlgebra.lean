import Mathlib
import OAI.Computability.QuantumFactoring.Primality

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open scoped BigOperators

/-- Exactly s coefficients with cyclic convolution, the concrete algebra
(Z/mZ)[X]/(X^s-1) used in the appendix. -/
abbrev Cyclic (R : Type*) [Semiring R] (s : ℕ) := AddMonoidAlgebra R (Fin s)

noncomputable def cyclicOf {R : Type*} [Semiring R] {s : ℕ} (v : Fin s → R) : Cyclic R s :=
  AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm v)

@[simp] lemma cyclicOf_coeff {R : Type*} [Semiring R] {s : ℕ} (v : Fin s → R) (i : Fin s) :
    (cyclicOf v).coeff i = v i := rfl

lemma cyclic_mul_coeff {R : Type*} [Semiring R] {s : ℕ} [NeZero s]
    (a b : Cyclic R s) (k : Fin s) :
    (a*b).coeff k = ∑ i : Fin s, a.coeff i * b.coeff (k-i) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum_fintype]
  · congr 1
    ext i
    rw [sub_eq_add_neg,add_comm k]
  · intro i
    simp

/-- The residue class of X. No exponentially long polynomial is constructed. -/
noncomputable def cyclicX {R : Type*} [Semiring R] (s : ℕ) [NeZero s] : Cyclic R s :=
  AddMonoidAlgebra.single 1 1

noncomputable def cyclicC {R : Type*} [Semiring R] (s : ℕ) [NeZero s] (a : R) : Cyclic R s :=
  AddMonoidAlgebra.single 0 a

lemma cyclicC_nat {R : Type*} [Semiring R] (s : ℕ) [NeZero s] (a : ℕ) :
    cyclicC s (a : R) = (a : Cyclic R s) := by
  induction a with
  | zero => simp [cyclicC]
  | succ a ih =>
    rw [Nat.cast_succ,Nat.cast_succ,← ih]
    simp [cyclicC,AddMonoidAlgebra.single_add,AddMonoidAlgebra.one_def]

/-- Primes satisfy the literal cyclic-array test by characteristic-p Frobenius. -/
lemma cyclic_prime_test {m s : ℕ} [NeZero s] (hm : m.Prime) (a : ℕ) :
    (cyclicX (R := ZMod m) s + cyclicC s (a : ZMod m))^m =
      cyclicX s ^m + cyclicC s (a : ZMod m) := by
  let : Fact m.Prime := ⟨hm⟩
  let : CharP (Cyclic (ZMod m) s) m :=
    charP_of_injective_ringHom (f := AddMonoidAlgebra.singleZeroRingHom)
      AddMonoidAlgebra.single_right_injective m
  rw [cyclicC_nat,add_pow_char,natCast_frobenius]

noncomputable def rootPower {F : Type*} [CommRing F] {s : ℕ} [NeZero s]
    (z : F) (hz : z^s=1) : Multiplicative (Fin s) →* F where
  toFun i := z^i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change z^((i.toAdd+j.toAdd).val)=z^i.toAdd.val*z^j.toAdd.val
    rw [Fin.val_add,← pow_eq_pow_mod _ hz,pow_add]

noncomputable def cyclicEval {R F : Type*} [Semiring R] [CommRing F]
    {s : ℕ} [NeZero s] (f : R →+* F) (z : F) (hz : z^s=1) : Cyclic R s →+* F :=
  AddMonoidAlgebra.liftNCRingHom f (rootPower z hz) (fun _ _ => Commute.all _ _)

lemma cyclicEval_X {R F : Type*} [Semiring R] [CommRing F]
    {s : ℕ} [NeZero s] (hs : 2 ≤ s) (f : R →+* F) (z : F) (hz : z^s=1) :
    cyclicEval f z hz (cyclicX s) = z := by
  simp [cyclicEval,cyclicX,rootPower, Nat.mod_eq_of_lt (by omega : 1 < s)]

lemma cyclicEval_C {R F : Type*} [Semiring R] [CommRing F]
    {s : ℕ} [NeZero s] (f : R →+* F) (z : F) (hz : z^s=1) (a : R) :
    cyclicEval f z hz (cyclicC s a) = f a := by
  simp [cyclicEval,cyclicC,rootPower]

/-- Equality of the two concrete coefficient arrays gives exactly the
introspective identity needed by the appendix's root-count contradiction. -/
lemma cyclic_test_introspective {F : Type*} [Field F] {m s p a : ℕ}
    [NeZero s] [CharP F p] (hs : 2 ≤ s) (hpm : p ∣ m)
    (h : (cyclicX (R := ZMod m) s + cyclicC s (a : ZMod m))^m =
      cyclicX s ^m + cyclicC s (a : ZMod m)) :
    Introspective s m (Polynomial.X+Polynomial.C (a : F)) := by
  intro z hz
  have hh := congrArg (cyclicEval (ZMod.castHom hpm F) z hz) h
  simpa only [map_pow,map_add,cyclicEval_X hs,cyclicEval_C,map_natCast,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_natCast] using hh

end ExactQuantumFactoring.Primality


end

end OAI
