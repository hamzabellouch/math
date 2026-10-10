import OAI.NumberTheory.Ostmann.Supply.SubsetReducedEnergy

namespace OAI

/-! # Summing the positive subset expansion inside the additive large sieve -/

namespace Ostmann
open scoped Classical BigOperators

theorem prime_subset_product_dvd_iff {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (R : Finset (Fin n)) (i : Fin n) : (p i ∣ ∏ j ∈ R, p j) ↔ i ∈ R := by
  rw [(Fact.out : (p i).Prime).prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨j, hj, hd⟩
    by_cases hij : i = j
    · simpa only [hij] using hj
    · exact ((Fact.out : (p i).Prime).coprime_iff_not_dvd.mp (hc hij) hd).elim
  · intro hi
    exact ⟨i, hi, dvd_rfl⟩

theorem prime_subset_product_injective {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Function.Injective (fun R : Finset (Fin n) => ∏ i ∈ R, p i) := by
  intro R T h
  ext i
  rw [← prime_subset_product_dvd_iff p hc R i,
    ← prime_subset_product_dvd_iff p hc T i]
  exact Iff.of_eq (congrArg (fun q => p i ∣ q) h)

/-- The complete double sum is bounded by the classical additive large sieve.
No centered-coordinate energy estimate is postulated in this step. -/
theorem prime_subset_sieve_bound (ls : PublishedAdditiveLargeSieve)
    {n M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (G : Finset (Finset (Fin n)))
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (hprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q)
    (ha : ∀ R ∈ G, ∀ x ∈ A, ∀ i ∈ R, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i) :
    (∑ R ∈ G, ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T *
      centeredSubsetEnergy p S T A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  have hpos (R : Finset (Fin n)) : 0 < ∏ i ∈ R, p i :=
    Finset.prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
  have he (R) (hR : R ∈ G) :
      (∑ T ∈ R.powerset, subsetSieveCoefficient p S R T *
        centeredSubsetEnergy p S T A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) =
      intervalSetReducedEnergy A J (∏ i ∈ R, p i) := by
    let : NeZero (∏ i ∈ R, p i) := ⟨(hpos R).ne'⟩
    rw [intervalSetReducedEnergy_eq_unitFrequencyEnergy]
    exact (subset_reduced_energy_expansion p S R hc A
      (fun x => J + (x.val : ℤ)) (ha R hR)).symm
  calc
    _ = ∑ R ∈ G, intervalSetReducedEnergy A J (∏ i ∈ R, p i) :=
      Finset.sum_congr rfl he
    _ = ∑ q ∈ G.image (fun R => ∏ i ∈ R, p i), intervalSetReducedEnergy A J q := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => prime_subset_product_injective p hc h
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy A J q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_Icc.mpr ⟨hpos R, hprod R hR⟩
      · intro q _ _
        exact intervalSetReducedEnergy_nonneg A J q
    _ ≤ _ := additiveSieve_probability_bound ls hM hQ A hA J

end Ostmann

end OAI
