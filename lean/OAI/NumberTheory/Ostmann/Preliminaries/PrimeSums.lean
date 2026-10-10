import OAI.NumberTheory.Ostmann.Preliminaries.DivisorCollision
import PrimeNumberTheoremAnd.Erdos970.MertensClassical

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open scoped BigOperators

abbrev PrimeUpTo (Q : ℕ) := {p : ℕ // p ∈ Q.primesLE}

instance primeUpToNeZero {Q : ℕ} (p : PrimeUpTo Q) : NeZero p.val :=
  ⟨(Nat.mem_primesLE.mp p.property).2.ne_zero⟩

theorem primeUpTo_prime {Q : ℕ} (p : PrimeUpTo Q) : p.val.Prime :=
  (Nat.mem_primesLE.mp p.property).2

theorem primeUpTo_le {Q : ℕ} (p : PrimeUpTo Q) : p.val ≤ Q :=
  (Nat.mem_primesLE.mp p.property).1

theorem sum_primeUpTo (Q : ℕ) (f : ℕ → ℝ) :
    (∑ p : PrimeUpTo Q, f p.val) = ∑ p ∈ Q.primesLE, f p := by
  exact Finset.sum_coe_sort _ _

theorem mertens_prime_sum (Q : ℕ) (hQ : 1 ≤ Q) :
    |(∑ p ∈ Q.primesLE, Real.log (p : ℝ) / p) - Real.log Q| ≤ Real.log 4 + 4 := by
  have hset : (Finset.Ioc 0 Q).filter Nat.Prime = Q.primesLE := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hle⟩, hp⟩
      exact ⟨hle, hp⟩
    · rintro ⟨hle, hp⟩
      exact ⟨⟨hp.pos, hle⟩, hp⟩
  have h := Erdos970.Mertens.sum_log_prime_div_eq_log (x := (Q : ℝ)) (by exact_mod_cast hQ)
  simpa only [Nat.floor_natCast, hset] using h

theorem mertens_prime_sum_lower (Q : ℕ) (hQ : 1 ≤ Q) :
    Real.log Q - (Real.log 4 + 4) ≤ ∑ p ∈ Q.primesLE, Real.log (p : ℝ) / p := by
  have := (abs_le.mp (mertens_prime_sum Q hQ)).1
  linarith

end Ostmann.Preliminaries

end OAI
