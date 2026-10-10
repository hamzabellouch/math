import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetSieve

namespace OAI

/-! # Amplifying the positive centered-energy expansion by extensions -/

namespace Ostmann
open scoped Classical BigOperators

theorem subset_energy_amplification {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (F G : Finset (Finset (Fin n))) (E : Finset (Fin n) → ℝ)
    (hE : ∀ T, 0 ≤ E T) (α C : ℝ)
    (hweight : ∀ T ∈ F, α ≤ ∑ R ∈ G,
      if T ⊆ R then subsetSieveCoefficient p S R T else 0)
    (hsieve : (∑ R ∈ G, ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T * E T) ≤ C) :
    α * (∑ T ∈ F, E T) ≤ C := by
  have hsmall (R : Finset (Fin n)) :
      (∑ T ∈ F, if T ⊆ R then subsetSieveCoefficient p S R T * E T else 0) ≤
        ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T * E T := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro T hT
      exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hT).2
    · intro T _ _
      exact mul_nonneg (subsetSieveCoefficient_nonneg p S R T (fun i _ => hS i)) (hE T)
  calc
    _ = ∑ T ∈ F, α * E T := Finset.mul_sum ..
    _ ≤ ∑ T ∈ F, (∑ R ∈ G,
        if T ⊆ R then subsetSieveCoefficient p S R T else 0) * E T := by
      apply Finset.sum_le_sum
      intro T hT
      exact mul_le_mul_of_nonneg_right (hweight T hT) (hE T)
    _ = ∑ R ∈ G, ∑ T ∈ F,
        if T ⊆ R then subsetSieveCoefficient p S R T * E T else 0 := by
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      exact Finset.sum_comm
    _ ≤ ∑ R ∈ G, ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T * E T :=
      Finset.sum_le_sum (fun R _ => hsmall R)
    _ ≤ C := hsieve

/-- Once the concrete extension weights are supplied, the actual centered
subset energies inherit the classical additive-sieve budget. -/
theorem prime_subset_energy_budget (ls : PublishedAdditiveLargeSieve)
    {n M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (F G : Finset (Finset (Fin n)))
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (hprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q)
    (ha : ∀ R ∈ G, ∀ x ∈ A, ∀ i ∈ R, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i)
    (α : ℝ) (hweight : ∀ T ∈ F, α ≤ ∑ R ∈ G,
      if T ⊆ R then subsetSieveCoefficient p S R T else 0) :
    α * (∑ T ∈ F, centeredSubsetEnergy p S T A
      (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) ≤
        ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  exact subset_energy_amplification p S hS F G _
    (fun T => centeredSubsetEnergy_nonneg p S T A _) α _ hweight
      (prime_subset_sieve_bound ls p hc S G hQ hM A hA J hprod ha)

end Ostmann

end OAI
