import OAI.Geometry.PeriodicTiling.WordRule
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

namespace PeriodicTilingThree

open scoped BigOperators

abbrev PrimeTag (p : ℕ) :=
  Channel p ⊕ (Channel p ⊕ (Σ i : Channel p, Label p i))

structure EncodingParameters (p : ℕ) where
  p_prime : Nat.Prime p
  p_large : 200 < p
  primeAt : PrimeTag p → ℕ
  prime_isPrime : ∀ t, Nat.Prime (primeAt t)
  prime_injective : Function.Injective primeAt
  prime_ne_p : ∀ t, primeAt t ≠ p
  seed_a_eq : ∀ t : Fin 2, primeAt (.inl (.inr t)) = t.val + 2
  seed_b_large : ∀ t : Fin 2, p ^ 4 < primeAt (.inr (.inl (.inr t)))
  blockA : ∀ i : Channel p, Label p i → ℕ
  blockB : ∀ i : Channel p, Label p i → ℕ
  blockA_pos : ∀ i j, 0 < blockA i j
  blockB_pos : ∀ i j, 0 < blockB i j
  digit_representation : ∀ i j,
    primeAt (.inr (.inr ⟨i, j⟩)) =
      blockA i j * primeAt (.inl i) + blockB i j * primeAt (.inr (.inl i))

namespace EncodingParameters

variable {p : ℕ} (E : EncodingParameters p)

def a (i : Channel p) : ℕ := E.primeAt (.inl i)
def b (i : Channel p) : ℕ := E.primeAt (.inr (.inl i))
def digitPrime (i : Channel p) (j : Label p i) : ℕ :=
  E.primeAt (.inr (.inr ⟨i, j⟩))

theorem a_prime (i : Channel p) : Nat.Prime (E.a i) := E.prime_isPrime _
theorem b_prime (i : Channel p) : Nat.Prime (E.b i) := E.prime_isPrime _
theorem digitPrime_prime (i : Channel p) (j : Label p i) :
    Nat.Prime (E.digitPrime i j) := E.prime_isPrime _

theorem a_pos (i : Channel p) : 0 < E.a i := (E.a_prime i).pos
theorem b_pos (i : Channel p) : 0 < E.b i := (E.b_prime i).pos
theorem digitPrime_pos (i : Channel p) (j : Label p i) :
    0 < E.digitPrime i j := (E.digitPrime_prime i j).pos

theorem a_two_le (i : Channel p) : 2 ≤ E.a i := (E.a_prime i).two_le
theorem b_two_le (i : Channel p) : 2 ≤ E.b i := (E.b_prime i).two_le

theorem seed_a (t : Fin 2) : E.a (.inr t) = t.val + 2 := E.seed_a_eq t

theorem digit_eq (i : Channel p) (j : Label p i) :
    E.digitPrime i j = E.blockA i j * E.a i + E.blockB i j * E.b i :=
  E.digit_representation i j

theorem prime_coprime {s t : PrimeTag p} (hst : s ≠ t) :
    Nat.Coprime (E.primeAt s) (E.primeAt t) :=
  (Nat.coprime_primes (E.prime_isPrime s) (E.prime_isPrime t)).2
    (fun h => hst (E.prime_injective h))

theorem prime_coprime_p (t : PrimeTag p) : Nat.Coprime (E.primeAt t) p :=
  (Nat.coprime_primes (E.prime_isPrime t) E.p_prime).2 (E.prime_ne_p t)

theorem a_coprime_b (i : Channel p) : Nat.Coprime (E.a i) (E.b i) := by
  apply E.prime_coprime
  simp

theorem digitPrime_pairwise (i : Channel p) :
    Pairwise (fun j j' : Label p i => Nat.Coprime (E.digitPrime i j) (E.digitPrime i j')) := by
  intro j j' hj
  apply E.prime_coprime
  intro he
  exact hj (by simpa using he)

section Finite

variable [NeZero p]

def r (i : Channel p) : ℕ := ∏ j : Label p i, E.digitPrime i j

theorem r_pos (i : Channel p) : 0 < E.r i := by
  exact Finset.prod_pos (fun j _ => E.digitPrime_pos i j)

instance a_neZero (i : Channel p) : NeZero (E.a i) := ⟨(E.a_pos i).ne'⟩
instance b_neZero (i : Channel p) : NeZero (E.b i) := ⟨(E.b_pos i).ne'⟩
instance digitPrime_neZero (i : Channel p) (j : Label p i) :
    NeZero (E.digitPrime i j) := ⟨(E.digitPrime_pos i j).ne'⟩
instance r_neZero (i : Channel p) : NeZero (E.r i) := ⟨(E.r_pos i).ne'⟩

theorem r_coprime_a (i j : Channel p) : Nat.Coprime (E.r i) (E.a j) := by
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply E.prime_coprime
  simp

theorem r_coprime_b (i j : Channel p) : Nat.Coprime (E.r i) (E.b j) := by
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply E.prime_coprime
  simp

theorem r_coprime_p (i : Channel p) : Nat.Coprime (E.r i) p := by
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  exact E.prime_coprime_p _

theorem r_pairwise_coprime : Pairwise (fun i j : Channel p => Nat.Coprime (E.r i) (E.r j)) := by
  intro i j hij
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro l
  apply E.prime_coprime
  intro he
  have hs : (⟨i, k⟩ : Σ i : Channel p, Label p i) = ⟨j, l⟩ :=
    Sum.inr.inj (Sum.inr.inj he)
  exact hij (congrArg Sigma.fst hs)

end Finite
end EncodingParameters
end PeriodicTilingThree

end OAI
