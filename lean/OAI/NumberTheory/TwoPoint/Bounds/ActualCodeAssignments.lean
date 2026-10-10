import OAI.NumberTheory.TwoPoint.Bounds.ActualSlotClasses
import OAI.NumberTheory.TwoPoint.Bounds.PositiveWordProbability

namespace OAI

/-! Actual code assignments preserve prime pools and the distinct-prime weight. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {R : ℕ}

lemma actualSlotPrime_mem_tuplePool (w : Fin R → SignedStep) (P : Finset ℕ)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P) (s : ActualPrimeSlot w)
    (hs : actualSlotKind w s = false) : actualSlotPrime w s ∈ P := by
  rcases s with ⟨i, p | p⟩
  · exact hP i p.property
  · cases hs

lemma actualSlotPrime_mem_paddingPool (w : Fin R → SignedStep) (Q : Finset ℕ)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q) (s : ActualPrimeSlot w)
    (hs : actualSlotKind w s = true) : actualSlotPrime w s ∈ Q := by
  rcases s with ⟨i, p | p⟩
  · cases hs
  · exact hQ i p.property

lemma actualPrimeSlotData_prime_image (w : Fin R → SignedStep) :
    univ.image (actualPrimeSlotData w).prime = univ.image (actualSlotPrime w) := by
  ext p
  constructor
  · rintro hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨(actualPrimeSlotEquiv w).symm i, mem_univ _, rfl⟩
  · rintro hp
    obtain ⟨s, _, rfl⟩ := mem_image.mp hp
    refine mem_image.mpr ⟨actualPrimeSlotEquiv w s, mem_univ _, ?_⟩
    change actualSlotPrime w ((actualPrimeSlotEquiv w).symm (actualPrimeSlotEquiv w s)) = _
    rw [Equiv.symm_apply_apply]

lemma actualPrimeSlot_support (w : Fin R → SignedStep)
    (ht : ∀ i, (w i).tuple ≠ 0) (hq : ∀ i, (w i).padding ≠ 0) :
    wordDivisorPrimeSupport (List.ofFn w) = univ.image (actualSlotPrime w) := by
  ext p
  simp only [wordDivisorPrimeSupport, mem_biUnion, List.mem_toFinset, List.mem_ofFn]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, hp⟩
    rw [Nat.primeFactors_mul (hq i) (ht i), mem_union] at hp
    rcases hp with hp | hp
    · exact mem_image.mpr ⟨⟨i, Sum.inr ⟨p, hp⟩⟩, mem_univ _, rfl⟩
    · exact mem_image.mpr ⟨⟨i, Sum.inl ⟨p, hp⟩⟩, mem_univ _, rfl⟩
  · rintro hp
    obtain ⟨⟨i, p | p⟩, _, rfl⟩ := mem_image.mp hp
    · refine ⟨w i, ⟨i, rfl⟩, ?_⟩
      rw [Nat.primeFactors_mul (hq i) (ht i), mem_union]
      exact Or.inr p.property
    · refine ⟨w i, ⟨i, rfl⟩, ?_⟩
      rw [Nat.primeFactors_mul (hq i) (ht i), mem_union]
      exact Or.inl p.property

/-- The encoded assignment pays exactly one reciprocal per distinct prime. -/
theorem actual_code_reciprocal_weight (w : Fin R → SignedStep)
    (ht : ∀ i, (w i).tuple ≠ 0) (hq : ∀ i, (w i).padding ≠ 0) :
    (∏ z : (actualPrimeSlotData w).code.usedClasses,
      ((actualPrimeSlotData w).prime z.val : ℝ)⁻¹) =
      ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹ := by
  rw [actualPrimeSlot_support w ht hq, ← actualPrimeSlotData_prime_image]
  rw [← PrimeSlotData.code_value_image, prod_image]
  exact fun z _ t _ h => (actualPrimeSlotData w).code_value_injective h

/-- Actual tuple and padding classes inhabit their separate numerical pools. -/
theorem actual_code_pool_assignments (w : Fin R → SignedStep) (P Q : Finset ℕ)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q) :
    ∃ a : (actualPrimeSlotData w).code.tupleClasses → P,
      ∃ b : {z : (actualPrimeSlotData w).code.usedClasses //
        z ∉ (actualPrimeSlotData w).code.tupleClasses} → Q,
      joinCoordinates (actualPrimeSlotData w).code.tupleClasses
        (fun z => (a z).val) (fun z => (b z).val) =
          fun z => (actualPrimeSlotData w).prime z.val := by
  let c := (actualPrimeSlotData w).code
  have htuple (z : c.tupleClasses) : (actualPrimeSlotData w).prime z.val.val ∈ P := by
    apply actualSlotPrime_mem_tuplePool w P hP
      ((actualPrimeSlotEquiv w).symm z.val.val)
    exact (mem_filter.mp z.property).2
  have hpadding (z : {z : c.usedClasses // z ∉ c.tupleClasses}) :
      (actualPrimeSlotData w).prime z.val.val ∈ Q := by
    apply actualSlotPrime_mem_paddingPool w Q hQ
      ((actualPrimeSlotEquiv w).symm z.val.val)
    have hn : ¬c.2.2.2 z.val.val = false := by
      intro hz
      exact z.property (mem_filter.mpr ⟨mem_univ _, hz⟩)
    change c.2.2.2 z.val.val = true
    cases he : c.2.2.2 z.val.val <;> simp_all
  refine ⟨(fun z => ⟨_, htuple z⟩), (fun z => ⟨_, hpadding z⟩), ?_⟩
  funext z
  dsimp only [joinCoordinates]
  split_ifs <;> rfl

end TwoPointCorrelations

end OAI
