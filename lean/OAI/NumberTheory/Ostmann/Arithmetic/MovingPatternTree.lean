import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleMap
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePairPatterns

namespace OAI

/-! # The actual pair of sampled trees after fixing an internal pattern -/

namespace Ostmann
open scoped Classical

/-- Fixed external labels and internal equality classes are kept separate.
The latter number depends only on depth, not on the bulk length. -/
def movingPatternSamples (C : Type*) (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) : MovingSampleSlots C n :=
  (movingSampleCoordinates C n).symm (fun i => pattern (side, i))

theorem movingPatternSamples_map {C A : Type*} (f : C → A) (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) :
    (movingPatternSamples C n pattern side).map f =
      movingPatternSamples A n (f ∘ pattern) side := by
  apply (movingSampleCoordinates A n).injective
  funext i
  rw [movingSampleCoordinates_map]
  simp only [movingPatternSamples, Equiv.apply_symm_apply, Function.comp_apply]

theorem movingPatternSamples_pair {C : Type*} (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C) :
    (movingPatternSamples C n pattern false, movingPatternSamples C n pattern true) =
      (movingSamplePairCoordinates C n).symm pattern := rfl

theorem treeLeafMap_list_comp {A B C : Type*} (f : A → B) (g : B → C)
    (n : ℕ) (x : TreeLeafTuple (List A) n) :
    treeLeafMap (List.map g) n (treeLeafMap (List.map f) n x) =
      treeLeafMap (List.map (g ∘ f)) n x := by
  induction n with
  | zero => exact List.map_map
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

def movingPatternSlotData {B C : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (side : Bool) : MovingSlotData (B ⊕ C) n :=
  buildMovingSlotData n t (treeLeafMap (List.map Sum.inl) n small)
    (treeLeafMap (List.map Sum.inl) n bulk)
    (movingPatternSamples (B ⊕ C) n (Sum.inr ∘ pattern) side)

/-- Evaluating the fixed pattern tree gives precisely the original sampled
constructor with those class values. No new sampler is introduced. -/
theorem movingPatternSlotData_evaluate {A B C : Type*} (external : B → A) (internal : C → A)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) :
    (movingPatternSlotData n t small bulk pattern side).map (Sum.elim external internal) =
      buildMovingSlotData n t (treeLeafMap (List.map external) n small)
        (treeLeafMap (List.map external) n bulk)
        (movingPatternSamples A n (internal ∘ pattern) side) := by
  unfold movingPatternSlotData
  rw [buildMovingSlotData_map, treeLeafMap_list_comp, treeLeafMap_list_comp,
    movingPatternSamples_map]
  rfl

theorem movingPatternSlotData_levels {B C : Type*} (tierB : B → ℕ) (tierC : C → ℕ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, n ≤ tierB i)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, n ≤ tierB i)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2) (side : Bool) :
    (movingPatternSlotData n t small bulk pattern side).Levels (Sum.elim tierB tierC) := by
  apply buildMovingSlotData_levels
  · intro i hi
    rw [flattenMovingSlots_map] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact hsmall j hj
  · intro i hi
    rw [flattenMovingSlots_map] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact hbulk j hj
  · apply movingSampleCoordinates_levels
    intro i
    exact htier (side, i)

end Ostmann

end OAI
