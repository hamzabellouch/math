import OAI.NumberTheory.Ostmann.Preliminaries.SieveWeightTruncation

namespace OAI

/-! # The retained Euler weights lie at the original integer sieve level -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def boundedSieveSubsets (P : Finset ℕ) (Q : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter fun U : Finset ℕ => (∏ p ∈ U, p) ≤ Q

 theorem sieve_subset_log_iff (U : Finset ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hU : ∀ p ∈ U, 0 < p) :
    (∑ p ∈ U, Real.log (p : ℝ)) ≤ Real.log (Q : ℝ) ↔ (∏ p ∈ U, p) ≤ Q := by
  have hprod : (0 : ℝ) < (∏ p ∈ U, p : ℕ) := by
    exact_mod_cast Finset.prod_pos hU
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have heq : (∑ p ∈ U, Real.log (p : ℝ)) = Real.log ((∏ p ∈ U, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    exact fun p hp => Nat.cast_ne_zero.mpr (hU p hp).ne'
  rw [heq, Real.log_le_log_iff hprod hQR]
  exact_mod_cast Iff.rfl

 theorem fixed_shift_bounded_weight (P : Finset ℕ) (j : ℝ) (Q : ℕ)
    (hj : 0 ≤ j) (hQ : 2 ≤ Q) (hP : ∀ p ∈ P, j < (p : ℝ))
    (hmean : j * (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ Real.log (Q : ℝ) / 2) :
    ((∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j)) / 2) ≤
      ∑ U ∈ boundedSieveSubsets P Q, ∏ p ∈ U, j / ((p : ℝ) - j) := by
  have hQpos : 0 < Q := by omega
  have hpos : ∀ p ∈ P, 0 < p := by
    intro p hp
    exact_mod_cast lt_of_le_of_lt hj (hP p hp)
  have hsets : P.powerset.filter (fun U : Finset ℕ =>
      (∑ p ∈ U, Real.log (p : ℝ)) ≤ Real.log (Q : ℝ)) = boundedSieveSubsets P Q := by
    ext U
    simp only [boundedSieveSubsets, Finset.mem_filter]
    apply and_congr_right
    intro hU
    exact sieve_subset_log_iff U Q hQpos (fun p hp => hpos p (Finset.mem_powerset.mp hU hp))
  have h := fixed_shift_short_weight P j Q hj (by exact_mod_cast hQ) hP hmean
  rwa [hsets] at h

end Ostmann

end OAI
