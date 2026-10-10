import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedPageDeletion
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternArithmeticData

namespace OAI

/-! # Support and arithmetic of the original regular-prime list -/

namespace Ostmann
open scoped Classical BigOperators

/-- The common top list, before its primes are drawn. -/
noncomputable def movingPatternRegularSlots {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n m : ℕ) (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B) :
    List (Fin (N + 1)) :=
  flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
    flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))

theorem movingPatternRegularSlots_external {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (i : Fin (N + 1))
    (hi : i ∈ movingPatternRegularSlots e n m small slot) :
    ∃ b, e.symm (.inl b) = i := by
  rcases List.mem_append.mp hi with hi | hi
  · rw [movingPatternFiniteSmall, flattenMovingSlots_map] at hi
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hi
    exact ⟨b, hb⟩
  · obtain ⟨j, hj⟩ := (mem_flatten_bulkSlotLeaves n m (movingPatternBulkEmbedding e slot) i).mp hi
    exact ⟨slot j, hj⟩

theorem naturalProduct_eq_finprod {σ : Type*} (value : σ → ℕ) (slots : List σ) :
    MovingSlotReversal.naturalProduct value slots = ∏ i : Fin slots.length, value (slots.get i) := by
  have h : List.ofFn (value ∘ slots.get) = slots.map value := by
    rw [← List.map_ofFn, List.ofFn_get]
  rw [MovingSlotReversal.naturalProduct, ← h, List.prod_ofFn]
  rfl

/-- The two history roots contain precisely the fixed regular slots. -/
theorem movingPatternFinBulkData_regular_perm {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C) (b : Bool) :
    (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern b).regularSlots.Perm
      (movingPatternRegularSlots e n m small slot) := by
  rw [movingPatternFinBulkData_build]
  have h := buildMovingSlotData_regular_perm n (t b)
    (movingPatternFiniteSmall e n small)
    (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))
    (movingPatternFiniteSamples e n pattern b)
  cases b <;> exact h

/-- Distinctness of the canonical regular enumeration comes from the original
support guard, so repeated independent draws need no extra assumption. -/
theorem movingPattern_regular_pairwise {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C) (value : Fin (N + 1) → ℕ)
    (outside : List ℕ) (b : Bool)
    (h : movingRegularOutsidePairwise value outside
      (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern b)) :
    Pairwise (fun i j : Fin (movingPatternRegularSlots e n m small slot).length =>
      (value ((movingPatternRegularSlots e n m small slot).get i)).Coprime
        (value ((movingPatternRegularSlots e n m small slot).get j))) := by
  let slots := movingPatternRegularSlots e n m small slot
  have hp := movingRegularOutsidePairwise_root value outside _ h
  have hperm := (movingPatternFinBulkData_regular_perm e t small slot pattern b).map value
  have hs : (slots.map value).Pairwise Nat.Coprime :=
    (hperm.pairwise_iff (R := Nat.Coprime) (fun h => h.symm)).mp hp
  have hlist : List.ofFn (value ∘ slots.get) = slots.map value := by
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← hlist, List.pairwise_ofFn] at hs
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hs hlt
  · exact (hs hgt).symm

/-- External regular primes are coprime to the separated internal/frequency
block on the original prior support. -/
theorem movingPattern_regular_arithmetic_coprime {A B C I : Type*}
    [Fintype C] [Fintype I] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (x : Fin (N + 1) → A) (r : ℕ) (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (hr : ∀ i, r.Coprime (prime (x i)))
    (hcross : ∀ b c, prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c))))
    (hspect : ∀ i j, prime (x j) ≠ p i) :
    (MovingSlotReversal.naturalProduct (fun i => prime (x i))
      (movingPatternRegularSlots e n m small slot)).Coprime
      (∏ b, movingArithmeticModuli r p (movingPatternInternalPrimes e prime x) Finset.univ b) := by
  let slots := movingPatternRegularSlots e n m small slot
  rw [naturalProduct_eq_finprod]
  apply movingArithmeticModuli_coprime_product r p (movingPatternInternalPrimes e prime x)
    (fun j : Fin slots.length => prime (x (slots.get j))) hp
    (movingPatternInternalPrimes_prime e prime hprime x) (fun _ => hprime _)
    (fun j => (hr _).symm)
  · intro j q hq
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨b, hb⟩ := movingPatternRegularSlots_external e small slot _ (List.get_mem slots j)
    exact hb ▸ hcross b c
  · exact fun j i => hspect i _

/-- The same one-prime conductor deletion used in the priors removes any
Page contribution from the original regular list. -/
theorem movingPattern_regular_page_projection {A B C I : Type*}
    [Fintype C] [Fintype I] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (x : Fin (N + 1) → A) (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (S : Finset ℤ) (V cutoff : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hcut : V < cutoff)
    (hlarge : ∀ i, cutoff ≤ prime (x i)) (z : Option PrimitiveRealZero)
    (hdelete : ∀ a, z = some a → ∀ q,
      deletedConductorPrime a.modulus cutoff = some q → ∀ i, prime (x i) ≠ q)
    (hdeletep : ∀ a, z = some a → ∀ q,
      deletedConductorPrime a.modulus cutoff = some q → ∀ i, p i ≠ q) :
    let M := ∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
      p (movingPatternInternalPrimes e prime x) Finset.univ b
    pageAtModulus (MovingSlotReversal.naturalProduct (fun i => prime (x i))
      (movingPatternRegularSlots e n m small slot) * M) z = pageAtModulus M z := by
  dsimp only
  let slots := movingPatternRegularSlots e n m small slot
  rw [naturalProduct_eq_finprod]
  apply frequencyModel_regular_page_projection S n V cutoff t hS hcut
    (movingPatternInternalPrimes e prime x) p (fun j : Fin slots.length => prime (x (slots.get j))) z
    (movingPatternInternalPrimes_prime e prime hprime x) hp (fun j => ⟨hprime _, hlarge _⟩)
  · intro a ha q hq hmem
    obtain ⟨c, _, heq⟩ := Finset.mem_image.mp hmem
    exact hdelete a ha q hq _ heq
  · exact fun a ha q hq i => (hdeletep a ha q hq i).symm
  · exact fun a ha q hq j => (hdelete a ha q hq _).symm

end Ostmann

end OAI
