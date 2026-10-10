import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Group.Pi.Lemmas

namespace OAI

/-!
# Actual primary components of the cyclic group of order u²

The prime set is the literal finite set of prime factors of `u`. The exponent
of each component is `(u ^ 2).factorization p`, hence twice the exponent in u.
Factorization and coprimality supply the hypotheses of the finite Chinese
remainder theorem. Its coordinates are the canonical reduction maps.

The generator of each primary component is the inverse image of its unit
coordinate vector. Its additive order is proved to be the full prime power,
and the complementary integer factor of u² is proved prime to p.
-/

noncomputable section

namespace CirculantHadamard.PrimeComponents

open scoped BigOperators

def primes (u : ℕ) : Finset ℕ := u.primeFactors

abbrev PrimeIndex (u : ℕ) := {p : ℕ // p ∈ primes u}

def exponent (u p : ℕ) : ℕ := (u ^ 2).factorization p

def order (u p : ℕ) : ℕ := p ^ exponent u p

abbrev Component (u : ℕ) (p : PrimeIndex u) := ZMod (order u p.val)

abbrev PrimaryProduct (u : ℕ) := (p : PrimeIndex u) → Component u p

theorem mem_primes {u p : ℕ} : p ∈ primes u ↔ p.Prime ∧ p ∣ u ∧ u ≠ 0 :=
  Nat.mem_primeFactors

theorem prime_of_mem {u p : ℕ} (hp : p ∈ primes u) : p.Prime :=
  (mem_primes.mp hp).1

theorem dvd_of_mem {u p : ℕ} (hp : p ∈ primes u) : p ∣ u :=
  (mem_primes.mp hp).2.1

theorem primes_nonempty {u : ℕ} (hu : 1 < u) : (primes u).Nonempty :=
  Nat.nonempty_primeFactors.mpr hu

theorem prime_ne_two_of_odd {u p : ℕ} (hu : Odd u) (hp : p ∈ primes u) : p ≠ 2 := by
  intro h
  apply hu.not_two_dvd_nat
  simpa only [h] using dvd_of_mem hp

theorem odd_of_mem {u p : ℕ} (hu : Odd u) (hp : p ∈ primes u) : Odd p :=
  (prime_of_mem hp).odd_of_ne_two (prime_ne_two_of_odd hu hp)

/-- The scalar exponent in local comparison is the exponent in u². -/
theorem exponent_eq_two_mul (u p : ℕ) : exponent u p = 2 * u.factorization p := by
  simp only [exponent, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

theorem exponent_pos {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    0 < exponent u p := by
  apply (prime_of_mem hp).factorization_pos_of_dvd (pow_ne_zero 2 hu.ne')
  exact (dvd_of_mem hp).trans (dvd_pow_self u (by decide : 2 ≠ 0))

theorem order_pos {u p : ℕ} (hp : p ∈ primes u) : 0 < order u p :=
  pow_pos (prime_of_mem hp).pos _

instance componentOrder_neZero (u : ℕ) (p : PrimeIndex u) : NeZero (order u p.val) :=
  ⟨(order_pos p.property).ne'⟩

theorem prime_dvd_order {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    p ∣ order u p := dvd_pow_self p (exponent_pos hu hp).ne'

theorem order_dvd_square (u p : ℕ) : order u p ∣ u ^ 2 :=
  Nat.ordProj_dvd (u ^ 2) p

/-- This is the full primary factor: the next power does not divide u². -/
theorem next_power_not_dvd {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    ¬p ^ (exponent u p + 1) ∣ u ^ 2 :=
  Nat.pow_succ_factorization_not_dvd (pow_ne_zero 2 hu.ne') (prime_of_mem hp)

def cofactor (u p : ℕ) : ℕ := u ^ 2 / order u p

theorem order_mul_cofactor (u p : ℕ) : order u p * cofactor u p = u ^ 2 := by
  exact Nat.mul_div_cancel' (order_dvd_square u p)

theorem cofactor_not_dvd {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    ¬p ∣ cofactor u p :=
  Nat.not_dvd_ordCompl (prime_of_mem hp) (pow_ne_zero 2 hu.ne')

theorem cofactor_coprime {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    Nat.Coprime p (cofactor u p) :=
  Nat.coprime_ordCompl (prime_of_mem hp) (pow_ne_zero 2 hu.ne')

theorem prod_order_finset (u : ℕ) (hu : 0 < u) :
    (∏ p ∈ primes u, order u p) = u ^ 2 := by
  have h := Nat.prod_factorization_pow_eq_self (pow_ne_zero 2 hu.ne')
  simpa only [Nat.prod_factorization_eq_prod_primeFactors,
    Nat.primeFactors_pow u (by decide : 2 ≠ 0), primes, order, exponent] using h

theorem prod_order (u : ℕ) (hu : 0 < u) :
    (∏ p : PrimeIndex u, order u p.val) = u ^ 2 := by
  change (∏ p : (primes u), order u p.val) = u ^ 2
  rw [Finset.prod_coe_sort]
  exact prod_order_finset u hu

theorem pairwise_coprime (u : ℕ) :
    Pairwise (fun p q : PrimeIndex u => Nat.Coprime (order u p.val) (order u q.val)) := by
  intro p q hpq
  exact Nat.coprime_pow_primes _ _ (prime_of_mem p.property) (prime_of_mem q.property)
    (fun h => hpq (Subtype.ext h))

/-- The actual finite Chinese remainder equivalence, with no chosen-map premise. -/
def crtRing (u : ℕ) (hu : 0 < u) : ZMod (u ^ 2) ≃+* PrimaryProduct u :=
  (ZMod.ringEquivCongr (prod_order u hu).symm).trans
    (ZMod.prodEquivPi (fun p : PrimeIndex u => order u p.val) (pairwise_coprime u))

def crt (u : ℕ) (hu : 0 < u) : ZMod (u ^ 2) ≃+ PrimaryProduct u :=
  (crtRing u hu).toAddEquiv

@[simp] theorem crt_intCast (u : ℕ) (hu : 0 < u) (z : ℤ) (p : PrimeIndex u) :
    crt u hu (z : ZMod (u ^ 2)) p = (z : Component u p) := by
  change (crtRing u hu (z : ZMod (u ^ 2))) p = _
  exact congrArg (fun y : PrimaryProduct u => y p) (map_intCast (crtRing u hu) z)

@[simp] theorem crt_natCast (u : ℕ) (hu : 0 < u) (z : ℕ) (p : PrimeIndex u) :
    crt u hu (z : ZMod (u ^ 2)) p = (z : Component u p) := by
  change (crtRing u hu (z : ZMod (u ^ 2))) p = _
  exact congrArg (fun y : PrimaryProduct u => y p) (map_natCast (crtRing u hu) z)

/-- Every CRT coordinate is literal reduction from ZMod(u²) to the full p-power. -/
theorem crt_apply (u : ℕ) (hu : 0 < u) (x : ZMod (u ^ 2)) (p : PrimeIndex u) :
    crt u hu x p = (ZMod.cast x : Component u p) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [crt_intCast, ZMod.cast_intCast (order_dvd_square u p.val)]

def primaryGenerator (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) : ZMod (u ^ 2) :=
  (crt u hu).symm (Pi.single p (1 : Component u p))

@[simp] theorem crt_primaryGenerator (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    crt u hu (primaryGenerator u hu p) = Pi.single p (1 : Component u p) :=
  (crt u hu).apply_symm_apply _

@[simp] theorem crt_primaryGenerator_same (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    crt u hu (primaryGenerator u hu p) p = 1 := by
  rw [crt_primaryGenerator, Pi.single_eq_same]

@[simp] theorem crt_primaryGenerator_ne (u : ℕ) (hu : 0 < u)
    (p q : PrimeIndex u) (hqp : q ≠ p) :
    crt u hu (primaryGenerator u hu p) q = 0 := by
  rw [crt_primaryGenerator, Pi.single_eq_of_ne hqp]

/-- The chosen primary generator has exactly the full primary order. -/
theorem primaryGenerator_addOrderOf (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    addOrderOf (primaryGenerator u hu p) = order u p.val := by
  rw [primaryGenerator, AddEquiv.addOrderOf_eq]
  have h := addOrderOf_injective (AddMonoidHom.single (Component u) p)
    (Pi.single_injective p) (1 : Component u p)
  exact h.trans (ZMod.addOrderOf_one (order u p.val))

end CirculantHadamard.PrimeComponents

end

end OAI
