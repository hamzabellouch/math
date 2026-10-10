import Mathlib

namespace OAI
/-!
Finite local arithmetic for a possible binary Goldbach sieve.  These results
count roots of the polynomial `x * (u - x)` and provide its multiplicative local
density.  They do not assert any prime-pair bound or positive density of Goldbach
numbers.
-/

noncomputable section

open scoped BigOperators

namespace Problem337

/-- Residue classes removed by the binary Goldbach sieve. -/
def GoldbachSieveRoot (u d : ℕ) :=
  {x : ZMod d // x * ((u : ZMod d) - x) = 0}

/-- Local number of roots of `x * (u - x)` modulo `d`. -/
def goldbachSieveRootCount (u d : ℕ) : ℕ :=
  Nat.card (GoldbachSieveRoot u d)

/-- The Chinese remainder theorem separates the local root conditions. -/
def goldbachSieveRootEquiv (u a b : ℕ) (hab : a.Coprime b) :
    GoldbachSieveRoot u (a * b) ≃
      GoldbachSieveRoot u a × GoldbachSieveRoot u b := by
  let e := ZMod.chineseRemainder hab
  apply (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change x * ((u : ZMod (a * b)) - x) = 0 ↔
    (e x).1 * ((u : ZMod a) - (e x).1) = 0 ∧
      (e x).2 * ((u : ZMod b) - (e x).2) = 0
  have h := e.injective.eq_iff (a := x * ((u : ZMod (a * b)) - x)) (b := 0)
  simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mk_zero_zero,
    Prod.mul_def, Prod.sub_def, Prod.fst_natCast, Prod.snd_natCast,
    Prod.mk.injEq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] using h.symm

/-- Root counts are multiplicative at coprime moduli, with no distribution hypothesis. -/
theorem goldbachSieveRootCount_mul (u a b : ℕ) (hab : a.Coprime b) :
    goldbachSieveRootCount u (a * b) =
      goldbachSieveRootCount u a * goldbachSieveRootCount u b := by
  unfold goldbachSieveRootCount
  rw [Nat.card_congr (goldbachSieveRootEquiv u a b hab), Nat.card_prod]

@[simp] theorem goldbachSieveRootCount_one (u : ℕ) :
    goldbachSieveRootCount u 1 = 1 := by
  unfold goldbachSieveRootCount GoldbachSieveRoot
  have e : {x : ZMod 1 // x * ((u : ZMod 1) - x) = 0} ≃ ZMod 1 :=
    Equiv.subtypeUnivEquiv (fun x => Subsingleton.elim _ _)
  rw [Nat.card_congr e, Nat.card_zmod]

/-- At a prime, the only roots are zero and the target residue. -/
theorem goldbachSieveRootCount_prime (u p : ℕ) (hp : p.Prime) :
    goldbachSieveRootCount u p = if p ∣ u then 1 else 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hroots : (Finset.univ.filter
      (fun x : ZMod p => x * ((u : ZMod p) - x) = 0)) = {0, (u : ZMod p)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mul_eq_zero, sub_eq_zero, Finset.mem_insert, Finset.mem_singleton]
    tauto
  unfold goldbachSieveRootCount GoldbachSieveRoot
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hroots]
  by_cases h : p ∣ u
  · simp [h, (ZMod.natCast_eq_zero_iff u p).mpr h]
  · have hne : (u : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff u p).not.mpr h
    simp [h, Ne.symm hne]

/-- A finite product of distinct primes gives the product of the local counts. -/
theorem goldbachSieveRootCount_prod_primes (u : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    goldbachSieveRootCount u (∏ p ∈ s, p) =
      ∏ p ∈ s, goldbachSieveRootCount u p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hpp := hs p (Finset.mem_insert_self p s)
      have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hpp (hsp q hq)).mpr
        intro heq
        exact hp (heq ▸ hq)
      rw [Finset.prod_insert hp, goldbachSieveRootCount_mul u p _ hcop,
        ih hsp, Finset.prod_insert hp]

/-- Exact squarefree local factor for the binary Goldbach sieve. -/
theorem goldbachSieveRootCount_squarefree (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d =
      ∏ p ∈ d.primeFactors, if p ∣ u then 1 else 2 := by
  calc
    goldbachSieveRootCount u d =
        goldbachSieveRootCount u (∏ p ∈ d.primeFactors, p) := by
          rw [Nat.prod_primeFactors_of_squarefree hd]
    _ = ∏ p ∈ d.primeFactors, goldbachSieveRootCount u p :=
      goldbachSieveRootCount_prod_primes u d.primeFactors
        (fun p hp => (Nat.mem_primeFactors.mp hp).1)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact goldbachSieveRootCount_prime u p (Nat.mem_primeFactors.mp hp).1

/-- The exact finite local root density, normalized as an arithmetic function. -/
def goldbachSieveDensity (u : ℕ) : ArithmeticFunction ℝ where
  toFun d := (goldbachSieveRootCount u d : ℝ) / (d : ℝ)
  map_zero' := by simp

@[simp] theorem goldbachSieveDensity_apply (u d : ℕ) :
    goldbachSieveDensity u d = (goldbachSieveRootCount u d : ℝ) / (d : ℝ) := rfl

/-- The finite local density has exactly the multiplicativity required by a sieve. -/
theorem goldbachSieveDensity_isMultiplicative (u : ℕ) :
    (goldbachSieveDensity u).IsMultiplicative := by
  constructor
  · simp
  · intro a b hab
    simp only [goldbachSieveDensity_apply, goldbachSieveRootCount_mul u a b hab,
      Nat.cast_mul, mul_div_mul_comm]

/-- The local density at a prime is `1/p` or `2/p`. -/
theorem goldbachSieveDensity_prime (u p : ℕ) (hp : p.Prime) :
    goldbachSieveDensity u p = if p ∣ u then 1 / (p : ℝ) else 2 / (p : ℝ) := by
  rw [goldbachSieveDensity_apply, goldbachSieveRootCount_prime u p hp]
  split_ifs <;> norm_num

/-- All prime local root densities are positive. -/
theorem goldbachSieveDensity_prime_pos (u p : ℕ) (hp : p.Prime) :
    0 < goldbachSieveDensity u p := by
  rw [goldbachSieveDensity_prime u p hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs <;> positivity

/-- At odd primes the sieve is nondegenerate. At two, this requires an even target. -/
theorem goldbachSieveDensity_prime_lt_one (u p : ℕ) (hp : p.Prime)
    (hparity : p = 2 → 2 ∣ u) : goldbachSieveDensity u p < 1 := by
  rw [goldbachSieveDensity_prime u p hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs with h
  · rw [div_lt_one hpR]
    exact_mod_cast hp.one_lt
  · have hp2 : 2 < p := by
      have := hp.two_le
      by_contra hnot
      have heq : p = 2 := by omega
      exact h (heq ▸ hparity heq)
    rw [div_lt_one hpR]
    exact_mod_cast hp2

end Problem337

end

end OAI
