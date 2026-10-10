import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotNodup
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenFrequencyAverage

namespace OAI

/-! # The original arithmetic support forces distinct bulk primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem prime_list_injective_of_pairwise {σ : Type*} (value : σ → ℕ)
    (L : List σ) (hprime : ∀ i ∈ L, (value i).Prime)
    (hp : (L.map value).Pairwise Nat.Coprime) :
    ∀ i ∈ L, ∀ j ∈ L, value i = value j → i = j := by
  have hn : (L.map value).Nodup := by
    apply hp.imp_of_mem
    intro a b ha hb hab
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact (Nat.coprime_primes (hprime i hi) (hprime j hj)).mp hab
  exact fun i hi j hj hij => List.inj_on_of_nodup_map hn hi hj hij

theorem buildMovingSlotData_injective_of_support {σ : Type*}
    (value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (outside : List ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hs : movingRegularOutsidePairwise value outside
      (buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples)) :
    Function.Injective (value ∘ slot) := by
  let T := buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples
  have hp : (T.regularSlots.map value).Pairwise Nat.Coprime := by
    have hroot : (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
      cases hT : T with
      | leaf s L => simpa only [T, hT, movingRegularOutsidePairwise,
          MovingSlotData.regularSlots] using hs
      | node s CL CR u left right =>
        have hs' := hs
        change movingRegularOutsidePairwise value outside T at hs'
        rw [hT] at hs'
        exact hs'.1
    exact (List.pairwise_append.mp hroot).1
  have hm (j) : slot j ∈ T.regularSlots := by
    apply (buildMovingSlotData_regular_perm n t small (bulkSlotLeaves n m slot) samples).mem_iff.mpr
    exact List.mem_append_right _ ((mem_flatten_bulkSlotLeaves n m slot _).mpr ⟨j, rfl⟩)
  intro i j hij
  exact slot.injective (prime_list_injective_of_pairwise value T.regularSlots
    (fun i _ => hprime i) hp (slot i) (hm i) (slot j) (hm j) hij)

/-- The frequency factor vanishes on collisions before any averaging or
resampling is performed. -/
theorem movingFrequencyPageAverage_zero_of_bulk_collision {σ : Type*}
    (value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (outside : List ℕ)
    (hprime : ∀ i, (value i).Prime) (hbad : ¬Function.Injective (value ∘ slot))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (T : Bool → MovingSlotData σ n)
    (hT : T false = buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples)
    (nodes : Bool → List MovingFormulaNode) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyPageAverage value outside F E T nodes R r input Q y = 0 := by
  have hsupport : ¬(∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      ∀ f ∈ nodes b, f.guard.frequencyBounds) := by
    intro hs
    apply hbad
    apply buildMovingSlotData_injective_of_support value n m slot t small samples outside hprime
    rw [← hT]
    exact (hs false).1
  rw [movingFrequencyPageAverage_core]
  simp only [hsupport, ite_false, zero_mul]

/-- Inserting the distinctness gate leaves the literal supported arithmetic
coefficient unchanged. -/
theorem movingFrequencyPageAverage_collision_gate {σ : Type*}
    (value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (outside : List ℕ)
    (hprime : ∀ i, (value i).Prime)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (T : Bool → MovingSlotData σ n)
    (hT : T false = buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples)
    (nodes : Bool → List MovingFormulaNode) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) (A : ℂ) :
    movingFrequencyPageAverage value outside F E T nodes R r input Q y * A =
      if Function.Injective (value ∘ slot) then
        movingFrequencyPageAverage value outside F E T nodes R r input Q y * A else 0 := by
  by_cases h : Function.Injective (value ∘ slot)
  · simp only [h, ite_true]
  · rw [ite_eq_right h, movingFrequencyPageAverage_zero_of_bulk_collision value n m slot
      t small samples outside hprime h F E T hT nodes R r input Q y, zero_mul]

end Ostmann

end OAI
