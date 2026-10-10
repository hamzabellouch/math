import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-! # Conductor support after deleting one large prime

For each exceptional conductor choose one prime divisor above the threshold,
if there is one, and exclude that value from the nongiant priors. A conductor
that still divides the arithmetic modulus is then supported on its frequency
block, with full prime-power multiplicity.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def deletedConductorPrime (D T : ℕ) : Option ℕ :=
  if h : ∃ p, p.Prime ∧ p ∣ D ∧ T ≤ p then some h.choose else none

theorem deletedConductorPrime_spec {D T p : ℕ}
    (h : deletedConductorPrime D T = some p) : p.Prime ∧ p ∣ D ∧ T ≤ p := by
  unfold deletedConductorPrime at h
  split at h
  next hex =>
    have hp : hex.choose = p := Option.some.inj h
    exact hp ▸ hex.choose_spec
  next => simp at h

/-- If the chosen large divisor was excluded, any surviving conductor divides
only the small frequency modulus. No squarefree assumption on the conductor
or on either modulus is needed. -/
theorem conductor_dvd_frequency_of_deletion (D Q R T : ℕ)
    (hQ : ∀ p, p.Prime → p ∣ Q → p < T)
    (hR : ∀ p, p.Prime → p ∣ R → T ≤ p)
    (hdeleted : ∀ p, deletedConductorPrime D T = some p → ¬p ∣ R)
    (hD : D ∣ Q * R) : D ∣ Q := by
  by_cases hlarge : ∃ p, p.Prime ∧ p ∣ D ∧ T ≤ p
  · have hsel : deletedConductorPrime D T = some hlarge.choose := by
      simp [deletedConductorPrime, hlarge]
    obtain ⟨hp, hpD, hpT⟩ := hlarge.choose_spec
    have hpQR := dvd_trans hpD hD
    rcases hp.dvd_mul.mp hpQR with hpQ | hpR
    · exact False.elim ((not_lt_of_ge hpT) (hQ _ hp hpQ))
    · exact False.elim (hdeleted _ hsel hpR)
  · have hcop : D.Coprime R := Nat.coprime_of_dvd fun p hp hpD hpR =>
      hlarge ⟨p, hp, hpD, hR p hp hpR⟩
    exact hcop.dvd_of_dvd_mul_left (by simpa only [Nat.mul_comm] using hD)

/-- Excluding a prime value excludes it from a product of powers of sampled
primes, even when the occurrence exponents exceed one. -/
theorem excluded_prime_not_dvd_product {p : ℕ} (hp : p.Prime)
    (P : Finset ℕ) (e : ℕ → ℕ) (hP : ∀ q ∈ P, q.Prime) (hex : p ∉ P) :
    ¬p ∣ ∏ q ∈ P, q ^ e q := by
  have hcop : p.Coprime (∏ q ∈ P, q ^ e q) := by
    apply Nat.Coprime.prod_right
    intro q hq
    apply Nat.Coprime.pow_right
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have heq := (Nat.prime_dvd_prime_iff_eq hp (hP q hq)).mp hd
    exact hex (heq ▸ hq)
  exact hp.coprime_iff_not_dvd.mp hcop

end Ostmann

end OAI
