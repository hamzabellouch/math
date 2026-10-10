import OAI.NumberTheory.Ostmann.Supply.ConcreteSubsetEnergyBudget
import OAI.NumberTheory.Ostmann.Supply.CenteredCoordinateSupport

namespace OAI

/-! # Restricting the centered-energy budget to the selected sparse primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem centeredSubsetEnergy_embedding {n m : ℕ} (p : Fin n → ℕ)
    [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (e : Fin m ↪ Fin n) (T : Finset (Fin m)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) :
    centeredSubsetEnergy (fun i => p (e i)) (fun i => S (e i)) T A
      (fun x i => a x (e i)) = centeredSubsetEnergy p S (T.image e) A a := by
  apply Complex.ofReal_injective
  rw [centeredSubsetEnergy_formula, centeredSubsetEnergy_formula]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  symm
  exact Finset.prod_image (fun i _ j _ hij => e.injective hij)

theorem lowMode_energy_embedding {n m : ℕ} (p : Fin n → ℕ)
    [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (e : Fin m ↪ Fin n) {ι : Type*} (A : Finset ι)
    (a : ι → ∀ i, ZMod (p i)) (K : ℕ) :
    countingVectorNorm (lowModeVector K (averagedCoordinates A
      (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => S (e i))
        (fun i => a x (e i))))) ^ 2 =
      ∑ T ∈ (Finset.univ.filter (fun T : Finset (Fin m) => T.card ≤ K)).image
        (fun T => T.image e), centeredSubsetEnergy p S T A a := by
  rw [lowMode_tensor_energy, Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs
    · exact centeredSubsetEnergy_embedding p S e T A a
    · rfl
  · intro T _ U _ h
    exact Finset.image_injective e.injective h

/-- The sparse tensor uses only its selected prime coordinates. Its low-mode
energy is bounded by the sieve on the full prime family, with no factor for
the number of unused coordinates. -/
theorem restricted_lowMode_energy_budget (ls : PublishedAdditiveLargeSieve)
    {n m M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (κ : ℕ → ℝ) (hκ : ∀ q ∈ Finset.univ.image p, 0 < κ q)
    (hκS : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hcover : ∀ q, Nat.Prime q → q ≤ Q → ∃ i, p i = q)
    (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (ha : ∀ x ∈ A, ∀ i, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i)
    (e : Fin m ↪ Fin n) (K : ℕ)
    (hprod : ∀ T : Finset (Fin m), T.card ≤ K → (∏ i ∈ T, p (e i)) ≤ Q)
    (hsmall : ∀ T : Finset (Fin m), T.card ≤ K →
      (∑ q ∈ T.image (fun i => p (e i)), (q : ℝ)⁻¹) ≤ 1 / 16)
    (B : ℝ) (hB : 0 < B)
    (hP : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)| / q) ≤ B / 16) :
    ((Q : ℝ) / 16 * Real.exp (-B)) *
      countingVectorNorm (lowModeVector K (averagedCoordinates A
        (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => S (e i))
          (fun i => ((J + (x.val : ℤ) : ℤ) : ZMod (p (e i))))))) ^ 2 ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  rw [lowMode_energy_embedding p S e A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i))) K]
  apply concrete_subset_energy_budget ls p hc S hS κ hκ hκS hQ hM hcover A hA J ha
  · intro U hU
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hU
    rw [Finset.prod_image (fun i _ j _ hij => e.injective hij)]
    exact hprod T (Finset.mem_filter.mp hT).2
  · intro U hU
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hU
    rw [Finset.image_image]
    exact hsmall T (Finset.mem_filter.mp hT).2
  · exact hB
  · exact hP

end Ostmann

end OAI
