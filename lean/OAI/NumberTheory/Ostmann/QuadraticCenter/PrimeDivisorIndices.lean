import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetSieve
import OAI.NumberTheory.Ostmann.Supply.WeightedMultiplierSupply

namespace OAI

/-! # Recovering squarefree integer multipliers as actual prime-index subsets -/

namespace Ostmann
open scoped Classical BigOperators

theorem coprime_prime_family_injective {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Function.Injective p := by
  intro i j he
  by_contra hij
  exact ((Fact.out : (p i).Prime).coprime_iff_not_dvd.mp (hc hij)) (dvd_of_eq he)

noncomputable def primeDivisorIndices {n : ℕ} (p : Fin n → ℕ) (u : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i ∣ u)

theorem primeDivisorIndices_image {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] {u : ℕ} (hu : u ≠ 0)
    (hcover : ∀ q ∈ u.primeFactors, ∃ i, p i = q) :
    (primeDivisorIndices p u).image p = u.primeFactors := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, (Finset.mem_filter.mp hi).2, hu⟩
  · intro hq
    obtain ⟨i, rfl⟩ := hcover q hq
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Nat.mem_primeFactors.mp hq).2.1⟩, rfl⟩

theorem primeDivisorIndices_product {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    {u : ℕ} (hu : Squarefree u) (hcover : ∀ q ∈ u.primeFactors, ∃ i, p i = q) :
    (∏ i ∈ primeDivisorIndices p u, p i) = u := by
  have he := Finset.prod_image (f := id) (s := primeDivisorIndices p u)
    (fun _ _ _ _ h => coprime_prime_family_injective p hc h)
  change (∏ q ∈ (primeDivisorIndices p u).image p, q) =
    (∏ i ∈ primeDivisorIndices p u, p i) at he
  rw [← he, primeDivisorIndices_image p hu.ne_zero hcover]
  exact Nat.prod_primeFactors_of_squarefree hu

theorem primeDivisorIndices_disjoint {n : ℕ} (p : Fin n → ℕ)
    (T : Finset (Fin n)) {u : ℕ} (hu : u.Coprime (∏ i ∈ T, p i))
    (hp : ∀ i, Nat.Prime (p i)) : Disjoint T (primeDivisorIndices p u) := by
  apply Finset.disjoint_left.mpr
  intro i hi hiu
  have hd : p i ∣ u := (Finset.mem_filter.mp hiu).2
  have he : p i ∣ ∏ j ∈ T, p j := Finset.dvd_prod_of_mem p hi
  exact (hp i).ne_one (Nat.eq_one_of_dvd_coprimes hu hd he)

end Ostmann

end OAI
