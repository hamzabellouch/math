import OAI.NumberTheory.JointDickman.Arithmetic.DivisorSumReindex

namespace OAI

/-! # Turning prime divisors into a prime--integer bilinear sum -/
namespace JointDickman
open Finset

theorem sum_prime_divisors_reindex {R : Type*} [AddCommMonoid R]
    (G : ℕ → ℕ → R) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ∑ p ∈ n.primeFactors, G p (n/p)) =
      ∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p), G p m := by
  have hprime : (Ioc 0 N).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp only [mem_filter,mem_Ioc,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hp0,hpN⟩,hp⟩
      exact ⟨hpN,hp⟩
    · rintro ⟨hpN,hp⟩
      exact ⟨⟨hp.pos,hpN⟩,hp⟩
  calc
    _ = ∑ n ∈ Ioc 0 N, ∑ p ∈ n.divisors, if p.Prime then G p (n/p) else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [Nat.primeFactors_eq_to_filter_divisors_prime,sum_filter]
    _ = ∑ p ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N/p), if p.Prime then G p m else 0 :=
      sum_Ioc_divisors_reindex (fun p m => if p.Prime then G p m else 0) N
    _ = ∑ p ∈ (Ioc 0 N).filter Nat.Prime, ∑ m ∈ Ioc 0 (N/p), G p m := by
      rw [sum_filter]
      apply sum_congr rfl
      intro p hp
      by_cases hpp : p.Prime <;> simp [hpp]
    _ = _ := by rw [hprime]

end JointDickman

end OAI
