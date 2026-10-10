import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctMomentBound

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem distinct_subset_normalized_error_bound {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (y : ι → ℤ)
    (hy : ∀ i ∈ I, y i = -1 ∨ y i = 0 ∨ y i = 1)
    (hI : 0 < I.card) {k : ℕ} (hk : 2 ≤ k) (heven : Even k) :
    |((k.factorial : ℝ) * (∑ s ∈ I.powersetCard k, ∏ i ∈ s, (y i : ℝ))) /
        (I.card : ℝ) ^ k - ((∑ i ∈ I, (y i : ℝ)) / I.card) ^ k| ≤
      (((k : ℝ) + 1) * (k : ℝ) ^ 2 / I.card) *
        (|(∑ i ∈ I, (y i : ℝ)) / I.card| + (k : ℝ) / Real.sqrt (I.card : ℝ)) ^ (k - 2) := by
  have hb := distinct_subset_moment_adaptive_error_bound I y hy hk
  have habspow := heven.pow_abs (∑ i ∈ I, (y i : ℝ))
  rw [← habspow] at hb
  have hn := normalize_adaptive_power_bound (by exact_mod_cast hI) hk hb
  rw [div_pow, habspow] at hn
  rw [div_pow]
  simpa only [abs_div, abs_of_pos (show (0 : ℝ) < I.card by exact_mod_cast hI)] using hn

theorem oriented_jacobi_trichotomy (ε a : ℤ) (p : ℕ)
    (hε : ε = -1 ∨ ε = 1) :
    ε * jacobiSym a p = -1 ∨ ε * jacobiSym a p = 0 ∨ ε * jacobiSym a p = 1 := by
  rcases hε with hε | hε <;>
    rcases jacobiSym.trichotomy a p with h | h | h <;> simp [hε, h]

theorem translated_jacobi_distinct_moment_error
    (P : Finset ℕ) (ε t : ℕ → ℤ) (n : ℤ)
    (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1)
    (hP : 0 < P.card) {k : ℕ} (hk : 2 ≤ k) (heven : Even k) :
    |((k.factorial : ℝ) *
        (∑ S ∈ P.powersetCard k, ∏ p ∈ S, ((ε p * jacobiSym (n - t p) p : ℤ) : ℝ))) /
        (P.card : ℝ) ^ k -
      ((∑ p ∈ P, ((ε p * jacobiSym (n - t p) p : ℤ) : ℝ)) / P.card) ^ k| ≤
      (((k : ℝ) + 1) * (k : ℝ) ^ 2 / P.card) *
        (|(∑ p ∈ P, ((ε p * jacobiSym (n - t p) p : ℤ) : ℝ)) / P.card| +
          (k : ℝ) / Real.sqrt (P.card : ℝ)) ^ (k - 2) :=
  distinct_subset_normalized_error_bound P (fun p => ε p * jacobiSym (n - t p) p)
    (fun p hp => oriented_jacobi_trichotomy (ε p) (n - t p) p (hε p hp)) hP hk heven

end Ostmann.QuadraticCenter

end OAI
