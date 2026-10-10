import OAI.NumberTheory.TotientAsymptotic.Arithmetic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors

namespace OAI

/-! Elementary discharge of the finite least-preimage seed. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma seed_prime_choices {p : ℕ} (hp : p.Prime) (hd : p-1 ∣ 2^18*257) :
    p=2 ∨ p=3 ∨ p=5 ∨ p=17 ∨ p=257 ∨ p=65537 := by
  obtain ⟨u,v,hu,hv,he⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨j,hj,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
  have hpEq : p=2^j*v+1 := by have := hp.two_le; omega
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 257)).mp hv with rfl|rfl
  · subst p
    interval_cases j <;> norm_num <;> norm_num at hp
  · subst p
    interval_cases j <;> norm_num <;> norm_num at hp

lemma seed_preimage_prime_choices {n p : ℕ} (hn : n.totient=2^18*257)
    (hp : p∈n.primeFactors) :
    p=2 ∨ p=3 ∨ p=5 ∨ p=17 ∨ p=257 ∨ p=65537 := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  apply seed_prime_choices hp'
  have hd := Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
  simpa only [Nat.totient_prime hp',hn] using hd

lemma seed_isTotient : IsTotient (2^18*257) := by
  refine ⟨2^11*257^2,by positivity,?_⟩
  rw [Nat.totient_mul (by norm_num : Nat.Coprime (2^11) (257^2)),
    Nat.totient_prime_pow Nat.prime_two (by omega),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 257) (by omega)]
  norm_num

end TotientAsymptotic

end

end OAI
