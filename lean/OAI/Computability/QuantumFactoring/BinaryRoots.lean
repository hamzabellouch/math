import Mathlib

namespace OAI

section
open scoped BigOperators


/-! Bounded binary-root search required by the appendix's perfect-power check.
The search uses only comparisons and powers with exponent at most the input
bit bound; no unbounded Nat.nthRoot primitive is used by the algorithm. -/
namespace ExactQuantumFactoring.Primality

def rootSearch (m e : ℕ) : (k guess : ℕ) → ℕ
  | 0, guess => guess
  | k+1, guess =>
      let next := guess+2^k
      rootSearch m e k (if next^e ≤ m then next else guess)

lemma rootSearch_spec {m e : ℕ} (_he : 0 < e) (k guess : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) :
    (rootSearch m e k guess)^e ≤ m ∧ m < (rootSearch m e k guess+1)^e := by
  induction k generalizing guess with
  | zero => simpa only [rootSearch,pow_zero] using And.intro hlo hhi
  | succ k ih =>
    simp only [rootSearch]
    by_cases hnext : (guess+2^k)^e ≤ m
    · rw [ite_eq_left hnext]
      apply ih _ hnext
      have hh : guess+2^k+2^k=guess+2^(k+1) := by rw [pow_succ]; omega
      rw [hh]
      exact hhi
    · rw [ite_eq_right hnext]
      exact ih _ hlo (by omega)

lemma rootSearch_eq {m e : ℕ} (he : 0 < e) (k guess b : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) (hb : b^e=m) :
    rootSearch m e k guess=b := by
  obtain ⟨hl,hh⟩ := rootSearch_spec he k guess hlo hhi
  have hl' : rootSearch m e k guess ≤ b :=
    (Nat.pow_le_pow_iff_left he.ne').mp (hl.trans_eq hb.symm)
  have hh' : b < rootSearch m e k guess+1 :=
    (Nat.pow_lt_pow_iff_left he.ne').mp (hb ▸ hh)
  omega

def boundedRoot (m e n : ℕ) : ℕ := rootSearch m e n 0

lemma boundedRoot_spec {m e n : ℕ} (he : 0 < e) (hm : m < 2^n) :
    (boundedRoot m e n)^e ≤ m ∧ m < (boundedRoot m e n+1)^e := by
  apply rootSearch_spec he n 0
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))

lemma boundedRoot_pow_eq {m e n b : ℕ} (he : 0 < e) (hm : m < 2^n) (hb : b^e=m) :
    boundedRoot m e n=b := by
  apply rootSearch_eq he n 0 b
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))
  · exact hb

lemma perfectPower_exponent_lt {m n b e : ℕ} (hm : m < 2^n) (hb : 2 ≤ b)
    (h : b^e=m) : e < n := by
  have hh : 2^e < 2^n := (Nat.pow_le_pow_left hb e).trans_lt (h ▸ hm)
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hh

end ExactQuantumFactoring.Primality


end

end OAI
