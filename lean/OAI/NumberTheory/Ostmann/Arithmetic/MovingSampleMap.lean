import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleCoordinateLevels
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotRelabel
import OAI.NumberTheory.Ostmann.Characters.TreeTupleProfiles

namespace OAI

/-! # Evaluating the fixed indexed sample tree

This identifies the original sampled prime tree with evaluation of fixed
slot data. Thus equality-pattern and polynomial arguments use the same
literal constructor as the sampled coefficient.
-/

namespace Ostmann
open scoped Classical

def MovingSampleSlots.map {A B : Type*} (f : A → B) :
    {n : ℕ} → MovingSampleSlots A n → MovingSampleSlots B n
  | _, .leaf => .leaf
  | n + 1, .node u l r =>
      .node (treeLeafMap (fun a : Fin 4 → A => f ∘ a) n u) (l.map f) (r.map f)

theorem flattenMovingSlots_map {A B : Type*} (f : A → B) (n : ℕ)
    (a : TreeLeafTuple (List A) n) :
    flattenMovingSlots n (treeLeafMap (List.map f) n a) = (flattenMovingSlots n a).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [treeLeafMap, flattenMovingSlots, List.map_append, ih]

theorem appendMovingSlotLeaves_map {A B : Type*} (f : A → B) (n : ℕ)
    (a b : TreeLeafTuple (List A) n) :
    treeLeafMap (List.map f) n (appendMovingSlotLeaves n a b) =
      appendMovingSlotLeaves n (treeLeafMap (List.map f) n a) (treeLeafMap (List.map f) n b) := by
  induction n with
  | zero => exact List.map_append
  | succ n ih => exact Prod.ext (ih a.1 b.1) (ih a.2 b.2)

theorem movingCompensationSlots_map {A B : Type*} (f : A → B) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) :
    movingCompensationSlots n (treeLeafMap (fun a : Fin 4 → A => f ∘ a) n a) =
      treeLeafMap (List.map f) n (movingCompensationSlots n a) := by
  induction n with
  | zero => exact List.map_ofFn.symm
  | succ n ih => exact Prod.ext (ih a.1) (ih a.2)

theorem buildMovingSlotData_map {A B : Type*} (f : A → B) (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List A) n) (a : MovingSampleSlots A n) :
    (buildMovingSlotData n t small bulk a).map f =
      buildMovingSlotData n t (treeLeafMap (List.map f) n small)
        (treeLeafMap (List.map f) n bulk) (a.map f) := by
  induction a with
  | leaf => exact congrArg (MovingSlotData.leaf t) List.map_append
  | node u l r hl hr =>
      simp only [buildMovingSlotData, MovingSlotData.map, MovingSampleSlots.map,
        treeLeafMap, movingCompensationSlots_map, flattenMovingSlots_map,
        List.map_append, hl, hr, appendMovingSlotLeaves_map]

theorem movingSampleCoordinates_map {A B : Type*} (f : A → B) {n : ℕ}
    (a : MovingSampleSlots A n) (i : MovingSampleIndex n) :
    movingSampleCoordinates B n (a.map f) i = f (movingSampleCoordinates A n a i) := by
  induction a with
  | leaf => exact Empty.elim i
  | @node n u l r hl hr =>
      rcases i with ⟨t, j⟩ | ⟨b, i⟩
      · exact congrFun (treeLeafTupleEquiv_map (fun a : Fin 4 → A => f ∘ a) n u t) j
      · cases b
        · exact hr i
        · exact hl i

/-- All sampled values are the evaluation of one fixed indexed tree. -/
theorem canonicalMovingSamples_map {A : Type*} (n : ℕ) (x : MovingSampleIndex n → A) :
    (canonicalMovingSamples n).map x = (movingSampleCoordinates A n).symm x := by
  apply (movingSampleCoordinates A n).injective
  funext i
  rw [movingSampleCoordinates_map, canonicalMovingSamples, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  rfl

end Ostmann

end OAI
