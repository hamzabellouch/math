import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleOccurrence
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOccurrenceRelabel
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternExternalPrior

namespace OAI

/-! # Finite coordinates for the actual internal-pattern tree pair -/

namespace Ostmann
open scoped Classical

theorem movingPairRepresentative_map_nonempty {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (i : σ)
    (base : MovingPairRepresentativeOccurrences T i) :
    Nonempty (MovingPairRepresentativeOccurrences (fun b => (T b).map f) (f i)) := by
  let o := (T base.1).occurrences.get base.2.val
  have ho : o.map f ∈ ((T base.1).map f).occurrences := by
    rw [MovingSlotData.occurrences_map]
    exact List.mem_map.mpr ⟨o, List.get_mem _ _, rfl⟩
  have hi : f i ∈ (o.map f).current.compensationSlots :=
    List.mem_map.mpr ⟨i, base.2.property, rfl⟩
  obtain ⟨k, hk, hko⟩ := List.mem_iff_getElem.mp ho
  refine ⟨⟨base.1, ⟨⟨k, hk⟩, ?_⟩⟩⟩
  simpa only [List.get_eq_getElem, hko] using hi

def movingPatternFinData {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) : MovingSlotData (Fin (N + 1)) n :=
  (movingPatternSlotData n (t side) (small side) (bulk side) pattern side).map e.symm

theorem movingPatternFinData_levels {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (tierB : B → ℕ) (tierC : C → ℕ) (n : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), n ≤ tierB i)
    (hbulk : ∀ b, ∀ i ∈ flattenMovingSlots n (bulk b), n ≤ tierB i)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2) (side : Bool) :
    (movingPatternFinData e n t small bulk pattern side).Levels ((Sum.elim tierB tierC) ∘ e) := by
  apply (MovingSlotData.levels_map e.symm (Sum.elim tierB tierC) ((Sum.elim tierB tierC) ∘ e)
    (fun i => by simp only [Function.comp_apply, Equiv.apply_symm_apply]) _).mpr
  exact movingPatternSlotData_levels tierB tierC n (t side) (small side) (bulk side) pattern (hsmall side) (hbulk side) htier side

/-- The base row is selected from a proved original occurrence, then mapped
into the finite coordinate system used by polynomial comparison. -/
noncomputable def movingPatternFinRepresentative {B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (n : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (c : C) :
    MovingPairRepresentativeOccurrences (movingPatternFinData e n t small bulk pattern)
      (e.symm (.inr c)) :=
  Classical.choice (movingPairRepresentative_map_nonempty e.symm _ (.inr c)
    (movingPatternRepresentative n t small bulk pattern rep c))

/-- Original class injectivity and separation from external slots imply the
unique-prime condition required by the simultaneous line comparison. -/
theorem movingPatternFin_unique {A B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hinj : Function.Injective prime)
    (x : Fin (N + 1) → A)
    (hclasses : Function.Injective (fun c => x (e.symm (.inr c))))
    (hcross : ∀ b c, prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c))))
    (c : C) (i : Fin (N + 1)) (hi : prime (x i) = prime (x (e.symm (.inr c)))) :
    i = e.symm (.inr c) := by
  obtain ⟨j, rfl⟩ := e.symm.surjective i
  cases j with
  | inl b => exact False.elim (hcross b c hi)
  | inr d => exact congrArg (fun c => e.symm (.inr c)) (hclasses (hinj hi))

end Ostmann

end OAI
