import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem exists_half_card_subset_prod_sq_le {ι : Type*} (S : Finset ι)
    (f : ι → ℕ) (hf : ∀ i ∈ S, 1 ≤ f i) :
    ∃ T ⊆ S, T.card = S.card / 2 ∧ (∏ i ∈ T, f i) ^ 2 ≤ ∏ i ∈ S, f i := by
  classical
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (Nat.div_le_self S.card 2)
  have hc : S.card / 2 ≤ (S \ T).card := by
    rw [Finset.card_sdiff_of_subset hT, hTc]
    omega
  obtain ⟨U, hU, hUc⟩ := Finset.exists_subset_card_eq hc
  have hUS : U ⊆ S := fun i hi => (Finset.mem_sdiff.mp (hU hi)).1
  have hdisj : Disjoint T U := by
    apply Finset.disjoint_left.mpr
    intro i hiT hiU
    exact (Finset.mem_sdiff.mp (hU hiU)).2 hiT
  have hp : (∏ i ∈ T, f i) * (∏ i ∈ U, f i) ≤ ∏ i ∈ S, f i := by
    rw [← Finset.prod_union hdisj]
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.union_subset hT hUS)
    exact fun i hi hnot => hf i hi
  by_cases hle : (∏ i ∈ T, f i) ≤ ∏ i ∈ U, f i
  · refine ⟨T, hT, hTc, ?_⟩
    nlinarith [Nat.mul_le_mul_left (∏ i ∈ T, f i) hle]
  · refine ⟨U, hUS, hUc, ?_⟩
    have hle' := le_of_not_ge hle
    nlinarith [Nat.mul_le_mul_left (∏ i ∈ U, f i) hle']

theorem exists_squarefree_half_divisor {n : ℕ} (hn : Squarefree n) :
    ∃ r : ℕ, r ∣ n ∧ Squarefree r ∧ r ^ 2 ≤ n ∧
      r.primeFactors.card = n.primeFactors.card / 2 := by
  obtain ⟨T, hT, hTc, hTs⟩ := exists_half_card_subset_prod_sq_le n.primeFactors
    (fun p => p) (fun p hp => (Nat.mem_primeFactors.mp hp).1.one_lt.le)
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hn
  have hd : (∏ p ∈ T, p) ∣ n := by
    rw [← hprod]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hT
  refine ⟨∏ p ∈ T, p, hd, hn.squarefree_of_dvd hd, ?_, ?_⟩
  · simpa only [hprod] using hTs
  · rw [Nat.primeFactors_prod (fun p hp => (Nat.mem_primeFactors.mp (hT hp)).1)]
    exact hTc

theorem half_prime_factor_weight_le {n r : ℕ}
    (hcard : r.primeFactors.card = n.primeFactors.card / 2)
    {u : ℝ} (hu : 1 ≤ u) :
    u ^ n.primeFactors.card ≤ u * (u ^ 2) ^ r.primeFactors.card := by
  have hc : n.primeFactors.card ≤ 2 * r.primeFactors.card + 1 := by omega
  calc
    u ^ n.primeFactors.card ≤ u ^ (2 * r.primeFactors.card + 1) :=
      pow_le_pow_right₀ hu hc
    _ = u * (u ^ 2) ^ r.primeFactors.card := by rw [pow_add, pow_mul, pow_one]; ring

theorem exists_coprime_half_divisor_weight {n L : ℕ} (hn : Squarefree n)
    (hcop : n.Coprime L) {u : ℝ} (hu : 1 ≤ u) :
    ∃ r : ℕ, r ∣ n ∧ Squarefree r ∧ r.Coprime L ∧ r ^ 2 ≤ n ∧
      r.primeFactors.card = n.primeFactors.card / 2 ∧
      u ^ n.primeFactors.card ≤ u * (u ^ 2) ^ r.primeFactors.card := by
  obtain ⟨r, hrd, hrs, hr2, hrc⟩ := exists_squarefree_half_divisor hn
  exact ⟨r, hrd, hrs, hcop.of_dvd_left hrd, hr2, hrc, half_prime_factor_weight_le hrc hu⟩

end Ostmann.QuadraticCenter

end OAI
