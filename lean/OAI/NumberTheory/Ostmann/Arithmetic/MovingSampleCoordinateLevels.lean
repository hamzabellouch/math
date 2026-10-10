import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleCoordinates

namespace OAI

/-! # Tier separation for the original indexed sample tree -/

namespace Ostmann
open scoped Classical

theorem movingCompensationSlots_forall {A : Type*} (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) (P : A → Prop)
    (h : ∀ t j, P (treeLeafTupleEquiv (Fin 4 → A) n a t j)) :
    ∀ i ∈ flattenMovingSlots n (movingCompensationSlots n a), P i := by
  induction n with
  | zero =>
      intro i hi
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
      exact h () j
  | succ n ih =>
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact ih a.1 (fun t j => h (.inl t) j) i hi
      · exact ih a.2 (fun t j => h (.inr t) j) i hi

/-- The sample constructor itself enforces the required tier of every
compensation occurrence. No assumption about an independently chosen tree
is needed when the labels are the actual sample coordinates. -/
theorem movingSampleCoordinates_levels {A : Type*} (tier : A → ℕ)
    (n : ℕ) (x : MovingSampleIndex n → A)
    (hx : ∀ i, tier (x i) = movingSampleTier i) :
    ((movingSampleCoordinates A n).symm x).Levels tier := by
  induction n with
  | zero => trivial
  | succ n ih =>
      let u := (treeLeafTupleEquiv (Fin 4 → A) n).symm (fun t j => x (.inl (t, j)))
      change (∀ i ∈ flattenMovingSlots n (movingCompensationSlots n u), tier i = n) ∧ _ ∧ _
      refine ⟨movingCompensationSlots_forall n u _ ?_, ?_, ?_⟩
      · intro t j
        have hu := congrFun (congrFun
          ((treeLeafTupleEquiv (Fin 4 → A) n).apply_symm_apply
            (fun t j => x (.inl (t, j)))) t) j
        change tier (treeLeafTupleEquiv (Fin 4 → A) n u t j) = n
        rw [hu]
        exact hx (.inl (t, j))
      · exact ih (fun i => x (.inr (true, i))) (fun i => hx (.inr (true, i)))
      · exact ih (fun i => x (.inr (false, i))) (fun i => hx (.inr (false, i)))

def canonicalMovingSamples (n : ℕ) : MovingSampleSlots (MovingSampleIndex n) n :=
  (movingSampleCoordinates (MovingSampleIndex n) n).symm id

theorem canonicalMovingSamples_levels (n : ℕ) :
    (canonicalMovingSamples n).Levels movingSampleTier :=
  movingSampleCoordinates_levels movingSampleTier n id (fun _ => rfl)

end Ostmann

end OAI
