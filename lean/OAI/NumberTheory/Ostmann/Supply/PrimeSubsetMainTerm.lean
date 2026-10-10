import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetSieve

namespace OAI

/-! # The positive empty-coordinate term in the subset large sieve -/

namespace Ostmann

open scoped Classical BigOperators

 theorem prime_subset_main_term (ls : PublishedAdditiveLargeSieve)
    {n M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (G : Finset (Finset (Fin n))) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (hprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q)
    (ha : ∀ R ∈ G, ∀ x ∈ A, ∀ i ∈ R, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i) :
    (∑ R ∈ G, ∏ i ∈ R, ((p i : ℝ) / (S i).card - 1)) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  apply le_trans _ (prime_subset_sieve_bound ls p hc S G hQ hM A hA J hprod ha)
  apply Finset.sum_le_sum
  intro R hR
  have hnonneg (T : Finset (Fin n)) (_hT : T ∈ R.powerset) :
      0 ≤ subsetSieveCoefficient p S R T *
        centeredSubsetEnergy p S T A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i))) :=
    mul_nonneg (subsetSieveCoefficient_nonneg p S R T (fun i _ => hS i))
      (centeredSubsetEnergy_nonneg p S T A _)
  have h := Finset.single_le_sum hnonneg (show ∅ ∈ R.powerset by simp)
  rw [centeredSubsetEnergy_empty p S A hA, mul_one] at h
  simpa only [subsetSieveCoefficient, Finset.prod_empty, one_mul, Finset.sdiff_empty] using h

end Ostmann

end OAI
