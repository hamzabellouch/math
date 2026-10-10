import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeDivisorIndices
import OAI.NumberTheory.Ostmann.Supply.SubsetEnergyAmplification

namespace OAI

/-! # Identifying the integer multiplier weights with sieve extensions -/

namespace Ostmann
open scoped Classical BigOperators

theorem multiplierRatioProduct_indices {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (κ : ℕ → ℝ) (u : ℕ) :
    multiplierRatioProduct (Finset.univ.image p) κ u =
      ∏ i ∈ primeDivisorIndices p u, κ (p i) := by
  unfold multiplierRatioProduct primeDivisorIndices
  rw [Finset.prod_image]
  · rw [Finset.prod_filter]
  · exact fun _ _ _ _ h => coprime_prime_family_injective p hc h

theorem subsetSieveCoefficient_extension {n : ℕ} (p : Fin n → ℕ)
    (S : ∀ i, Finset (ZMod (p i))) (T I : Finset (Fin n)) (hTI : Disjoint T I) :
    subsetSieveCoefficient p S (T ∪ I) T =
      (∏ i ∈ T, (p i : ℝ)) * ∏ i ∈ I, ((p i : ℝ) / (S i).card - 1) := by
  have he : (T ∪ I) \ T = I := by
    ext i
    have hd : i ∈ T → i ∉ I := fun hi hiI => (Finset.disjoint_left.mp hTI) hi hiI
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  simp only [subsetSieveCoefficient, he]

theorem primeIndexExtension_product {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (T : Finset (Fin n)) {u : ℕ} (hu : Squarefree u)
    (hcover : ∀ q ∈ u.primeFactors, ∃ i, p i = q)
    (hcop : u.Coprime (∏ i ∈ T, p i)) :
    (∏ i ∈ T ∪ primeDivisorIndices p u, p i) = (∏ i ∈ T, p i) * u := by
  rw [Finset.prod_union (primeDivisorIndices_disjoint p T hcop (fun _ => Fact.out)),
    primeDivisorIndices_product p hc hu hcover]

theorem primeIndexExtension_injective {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (T : Finset (Fin n)) (D : Finset ℕ)
    (hsq : ∀ u ∈ D, Squarefree u)
    (hcover : ∀ u ∈ D, ∀ q ∈ u.primeFactors, ∃ i, p i = q)
    (hcop : ∀ u ∈ D, u.Coprime (∏ i ∈ T, p i)) :
    Set.InjOn (fun u => T ∪ primeDivisorIndices p u) D := by
  intro u hu v hv huv
  have he := congrArg (fun R : Finset (Fin n) => ∏ i ∈ R, p i) huv
  rw [primeIndexExtension_product p hc T (hsq u hu) (hcover u hu) (hcop u hu),
    primeIndexExtension_product p hc T (hsq v hv) (hcover v hv) (hcop v hv)] at he
  exact Nat.eq_of_mul_eq_mul_left
    (Finset.prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)) he

theorem primeIndexExtension_coefficient {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (κ : ℕ → ℝ)
    (hκ : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (T : Finset (Fin n)) {u : ℕ} (hcop : u.Coprime (∏ i ∈ T, p i)) :
    subsetSieveCoefficient p S (T ∪ primeDivisorIndices p u) T =
      (∏ i ∈ T, (p i : ℝ)) * multiplierRatioProduct (Finset.univ.image p) κ u := by
  rw [subsetSieveCoefficient_extension p S T _
    (primeDivisorIndices_disjoint p T hcop (fun _ => Fact.out)),
    multiplierRatioProduct_indices p hc]
  simp only [hκ]

end Ostmann

end OAI
