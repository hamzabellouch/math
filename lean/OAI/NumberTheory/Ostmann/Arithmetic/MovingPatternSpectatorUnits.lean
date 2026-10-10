import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkData
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSpectatorGain

namespace OAI

/-! # The spectator unit conditions from the actual pattern coordinates -/

namespace Ostmann
open scoped Classical

theorem movingSlotValues_unit {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (n : ℕ) (small : TreeLeafTuple (List σ) n)
    (h : ∀ i ∈ flattenMovingSlots n small, (value i : ZMod q) ≠ 0) :
    ((treeLeafProduct n (movingSlotValues value n small) : ℕ) : ZMod q) ≠ 0 := by
  rw [← movingSlotValues_flatten, MovingSlotReversal.naturalProduct, Nat.cast_list_prod, List.map_map]
  apply List.prod_ne_zero
  intro hz
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hz
  exact h i hi he

theorem MovingSampleSlots.values_units_of_coordinates {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) {n : ℕ} (samples : MovingSampleSlots σ n)
    (h : ∀ i, (value (movingSampleCoordinates σ n samples i) : ZMod q) ≠ 0) :
    (samples.values value).UnitsAt q := by
  induction samples with
  | leaf => trivial
  | @node n u l r ihL ihR =>
    refine ⟨?_, ihL (fun i => h (.inr (true, i))), ihR (fun i => h (.inr (false, i)))⟩
    rw [← movingCompensationValues_product]
    apply movingSlotValues_unit
    apply movingCompensationSlots_forall
    intro a j
    exact h (.inl (a, j))

theorem movingPatternFiniteSamples_units {B C : Type*} {N n q : ℕ} [Fact q.Prime]
    (e : Fin (N + 1) ≃ B ⊕ C) (value : Fin (N + 1) → ℕ)
    (pattern : Bool × MovingSampleIndex n → C)
    (h : ∀ c, (value (e.symm (.inr c)) : ZMod q) ≠ 0) (b : Bool) :
    ((movingPatternFiniteSamples e n pattern b).values value).UnitsAt q := by
  apply MovingSampleSlots.values_units_of_coordinates
  intro i
  simpa only [movingPatternFiniteSamples, movingPatternSamples, Equiv.apply_symm_apply,
    Function.comp_apply] using h (pattern (b, i))

theorem movingPatternFiniteSmall_unit {B C : Type*} {N n q : ℕ} [Fact q.Prime]
    (e : Fin (N + 1) ≃ B ⊕ C) (value : Fin (N + 1) → ℕ)
    (small : TreeLeafTuple (List B) n)
    (h : ∀ b ∈ flattenMovingSlots n small, (value (e.symm (.inl b)) : ZMod q) ≠ 0) :
    ((treeLeafProduct n (movingSlotValues value n (movingPatternFiniteSmall e n small)) : ℕ) : ZMod q) ≠ 0 := by
  apply movingSlotValues_unit
  intro i hi
  rw [movingPatternFiniteSmall, flattenMovingSlots_map] at hi
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
  exact h b hb

end Ostmann

end OAI
