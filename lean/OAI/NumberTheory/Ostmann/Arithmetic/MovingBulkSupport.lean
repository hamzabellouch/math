import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotNodup

namespace OAI

/-! # Removing the bulk coprimality tests in the literal sampled tree -/

namespace Ostmann
open scoped Classical

theorem buildMovingSlotData_regular_support_frozen {σ : Type*} (n m : ℕ)
    (tier : σ → ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (base value : σ → ℕ) (hv : ∀ i ∉ Set.range slot, value i = base i)
    (hprime : ∀ i, (value i).Prime)
    (hinj : Function.Injective (value ∘ slot))
    (hsep : ∀ i ∈ Set.range slot, ∀ j ∉ Set.range slot, value i ≠ value j)
    (outside : List ℕ) (hout : ∀ j p, p ∈ outside → (value (slot j)).Coprime p)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (hsmallTier : ∀ i ∈ flattenMovingSlots n small, n ≤ tier i)
    (hslotTier : ∀ j, n ≤ tier (slot j)) (hsamples : samples.Levels tier) :
    movingRegularOutsidePairwise value outside
        (buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples) ↔
      movingNonbulkOutsidePairwise base (fun i => decide (i ∈ Set.range slot)) outside
        (buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples) := by
  let bulk := fun i => decide (i ∈ Set.range slot)
  have htrue (i : σ) : bulk i = true ↔ i ∈ Set.range slot := by simp [bulk]
  have hfalse (i : σ) : bulk i = false ↔ i ∉ Set.range slot := by simp [bulk]
  have hb (j) : bulk (slot j) = true := (htrue _).mpr ⟨j, rfl⟩
  have hgrade (i) (hi : bulk i = true) : n ≤ tier i := by
    obtain ⟨j, rfl⟩ := (htrue i).mp hi
    exact hslotTier j
  have hn := buildMovingSlotData_bulk_nodup n m bulk tier slot hb hgrade t small samples
    (fun i hi => (hfalse i).mpr (hsmall i hi)) hsmallTier hsamples
  apply movingRegularOutsidePairwise_frozen value base bulk outside _
    (fun i hi => hv i ((hfalse i).mp hi)) (fun _ _ i _ => hprime i) hn
    (bulk_value_injective value bulk slot (fun i hi => (htrue i).mp hi) hinj)
  · intro L hL i hi j hj hij
    cases hbi : bulk i with
    | true =>
      have hbj : bulk j = false := by
        cases hbj : bulk j with
        | false => rfl
        | true => exact False.elim (hij (hbi.trans hbj.symm))
      exact hsep i ((htrue i).mp hbi) j ((hfalse j).mp hbj)
    | false =>
      have hbj : bulk j = true := by
        cases hbj : bulk j with
        | false => exact False.elim (hij (hbi.trans hbj.symm))
        | true => rfl
      exact Ne.symm (hsep j ((htrue j).mp hbj) i ((hfalse i).mp hbi))
  · intro L hL i hi hbi p hp
    obtain ⟨j, rfl⟩ := (htrue i).mp hbi
    exact hout j p hp

end Ostmann

end OAI
