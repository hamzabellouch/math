import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterConcreteMoments

namespace OAI

/-! # A rational common center from witnessed prime tuples

This is the finite counting step in the paragraph “One common centre for many
primes” of Section 3 of the manuscript. The hypotheses are the actual family
of witnessed tuples and numerical inequalities; the factorial moments and
intersection estimates are proved from the congruences.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def liftMomentUpper (J r H Z : ℕ) : ℝ :=
  (J.descFactorial r : ℝ) * ((2 * (H : ℝ) + 1) / (Z : ℝ) ^ r + 1)

theorem exists_commonCenter_of_tuple_lifts (P : Finset ℕ)
    (a : ℕ) (ha : 0 < a) (t : ℕ → ℤ) (k d K H Z : ℕ) (hd : d ≤ k + 1)
    (A V : ℝ) (hA : 0 < A) (hV : 0 < V) (hZ : 0 < Z)
    (hprime : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, a < p)
    (hmin : ∀ p ∈ P, Z ≤ p) (hlog : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hbudget : Real.log (2 * (H : ℝ)) < (K + 1 : ℕ) * V)
    (hsmall : 2 * K * (P.card : ℝ) ≤ A ^ 2)
    (E : Finset (Fin (k + 1) ↪ P))
    (hlift : ∀ e ∈ E, ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
      ∀ i, ((e i).1 : ℤ) ∣ n - a * t (e i).1)
    (hpositive : 0 < (E.card : ℝ) - A ^ d * liftMomentUpper P.card (k + 1 - d) H Z) :
    ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1), ∃ h : ℤ, ∃ m : ℕ,
      0 < m ∧ m ≤ a ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
      A ≤ ((matchingPrimes P a t n).card : ℝ) ∧
      (E.card : ℝ) - A ^ d * liftMomentUpper P.card (k + 1 - d) H Z ≤
        2 * P.card * ((matchingPrimes P a t n).card : ℝ) ^ k ∧
      ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
        let _ : Fact p.Prime := ⟨hprime p (Finset.mem_filter.mp hp).1⟩
        (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  exact exists_commonCenter_of_lift_moments P (Finset.Ico (-(H : ℤ)) (H + 1))
    a ha t k d K hd A (liftMomentUpper P.card (k + 1 - d) H Z) E.card V
    hA hV hprime hap hlog
    (fun n hn m hm hne => liftInterval_log_difference H K V hbudget n m hn hm hne)
    hsmall (interval_factorial_moment_le P hprime a t (k + 1 - d) H Z hZ hmin)
    (interval_factorial_moment_ge P a t (k + 1) H E hlift) hpositive

end Ostmann

end OAI
