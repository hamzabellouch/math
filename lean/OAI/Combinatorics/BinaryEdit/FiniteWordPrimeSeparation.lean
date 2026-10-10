import OAI.Combinatorics.BinaryEdit.FiniteTreeInstantiation
import OAI.Combinatorics.BinaryEdit.PrimeSeparation

namespace OAI

/-!
# Prime separation for finite-tree words

Prime-divisor counting controls the exceptions in the separation induction.
-/

namespace TreeEdit.BinaryLower.FiniteTree

open scoped BigOperators

/-- Appending a child multiplies the actual word period by that child's prime. -/
theorem wordPeriod_append_child {m k : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ i : Fin m) (p : List (Fin m))
    (hp : p.length < k) :
    wordPeriod primes i₀ (p ++ [i]) =
      wordPeriod primes i₀ p * primes ⟨p.length, hp⟩ i := by
  simpa only [wordPeriod, List.length_append, List.length_singleton,
    extendPrefix_append i₀ i p hp] using
    FiniteVectors.prefixPeriod_child primes p.length hp (extendPrefix i₀ p) i

/-- Prefix/current-level coprimality transported to the actual word period. -/
theorem wordPeriod_coprime_level {m k : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (p : List (Fin m))
    (hp : p.length < k)
    (hinj : Function.Injective (fun z : Fin k × Fin m => primes z.1 z.2))
    (hprime : ∀ q i, Nat.Prime (primes q i)) (hodd : ∀ q i, primes q i ≠ 2) :
    Nat.Coprime (wordPeriod primes i₀ p)
      (FiniteVectors.levelProduct primes ⟨p.length, hp⟩) :=
  FiniteVectors.prefixPeriod_coprime_level primes hinj hprime hodd
    p.length hp (extendPrefix i₀ p)

/-- At least half the actual children have a nonzero relative row shift.
All prefixes, all legal row pairs (including equal rows), and every nonzero
parent-period residue are included. No upper bound on primes is needed. -/
theorem finiteWord_half_children {k : ℕ} (hk : 2 ≤ k)
    (primes : Fin k → Fin (20 * k) → ℕ) (i₀ : Fin (20 * k))
    (p : List (Fin (20 * k))) (hp : p.length < k)
    (hinj : Function.Injective
      (fun z : Fin k × Fin (20 * k) => primes z.1 z.2))
    (hprime : ∀ q i, Nat.Prime (primes q i))
    (hlarge : ∀ q i, k ^ 4 ≤ primes q i)
    (a b : Fin (k ^ (20 * k))) (t : ℤ)
    (ht : ¬ (wordPeriod primes i₀ p : ℤ) ∣ t) :
    20 * k ≤ 2 * (Finset.univ.filter fun i : Fin (20 * k) =>
      ¬ (wordPeriod primes i₀ (p ++ [i]) : ℤ) ∣
        (b : ℤ) - (a : ℤ) +
          t * (FiniteVectors.levelProduct primes ⟨p.length, hp⟩ : ℤ)).card := by
  classical
  have hodd : ∀ q i, primes q i ≠ 2 := by
    intro q i heq
    have hpow : 2 ^ 4 ≤ k ^ 4 := Nat.pow_le_pow_left hk 4
    have hlow := hlarge q i
    rw [heq] at hlow
    norm_num at hpow
    omega
  have hlevelinj : Function.Injective (primes ⟨p.length, hp⟩) := by
    intro i j hij
    have h := @hinj (⟨p.length, hp⟩, i) (⟨p.length, hp⟩, j) hij
    exact congrArg Prod.snd h
  have hc := wordPeriod_coprime_level primes i₀ p hp hinj hprime hodd
  have hcount := PrimeSeparation.finite_tree_row_pair_nondivisibility
    k (wordPeriod primes i₀ p) (primes ⟨p.length, hp⟩) a.val b.val t hk
    (hprime ⟨p.length, hp⟩) hlevelinj (hlarge ⟨p.length, hp⟩)
    a.isLt b.isLt hc ht
  have hcount' : 10 * k ≤ (Finset.univ.filter fun i : Fin (20 * k) =>
      ¬ (wordPeriod primes i₀ (p ++ [i]) : ℤ) ∣
        (b : ℤ) - (a : ℤ) +
          t * (FiniteVectors.levelProduct primes ⟨p.length, hp⟩ : ℤ)).card := by
    simpa only [wordPeriod_append_child primes i₀ _ p hp, FiniteVectors.levelProduct]
      using hcount
  omega

end TreeEdit.BinaryLower.FiniteTree

end OAI
