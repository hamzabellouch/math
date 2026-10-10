import Mathlib
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Executable finite products of child-state lists

The wide-action lists use this literal recursive Cartesian product.
Their coordinates are child labels, so duplicate interval labels remain
distinct coordinates.
-/

namespace EditApproximation



theorem finiteAssignments_complete {α : Type*} (M : ℕ) (choices : Fin M → List α)
    (action : Fin M → α) (ha : ∀ i, action i ∈ choices i) :
    action ∈ finiteAssignments M choices := by
  induction M with
  | zero =>
    have haction : action = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp only [finiteAssignments, haction, List.mem_singleton]
  | succ M ih =>
    apply List.mem_flatMap.mpr
    refine ⟨action 0, ha 0, List.mem_map.mpr ?_⟩
    refine ⟨fun i => action i.succ, ih _ _ (fun i => ha i.succ), ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem finiteAssignments_sound {α : Type*} (M : ℕ) (choices : Fin M → List α)
    (action : Fin M → α) (ha : action ∈ finiteAssignments M choices) :
    ∀ i, action i ∈ choices i := by
  induction M with
  | zero => intro i; exact Fin.elim0 i
  | succ M ih =>
    obtain ⟨head, hhead, hrest⟩ := List.mem_flatMap.mp ha
    obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp hrest
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hhead
    · exact ih _ _ htail _

theorem finiteAssignments_length_le {α : Type*} (M K : ℕ)
    (choices : Fin M → List α) (hchoices : ∀ i, (choices i).length ≤ K) :
    (finiteAssignments M choices).length ≤ K ^ M := by
  induction M with
  | zero => simp only [finiteAssignments, List.length_singleton, pow_zero, le_refl]
  | succ M ih =>
    have htail := ih (fun i => choices i.succ) (fun i => hchoices i.succ)
    have hflat (entries : List α) :
        (entries.flatMap fun head =>
          (finiteAssignments M (fun i => choices i.succ)).map
            fun tail => (Fin.cons head tail : Fin (M + 1) → α)).length =
        entries.length * (finiteAssignments M (fun i => choices i.succ)).length := by
      induction entries with
      | nil => simp
      | cons head rest ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
        ring
    rw [finiteAssignments, hflat, pow_succ]
    nlinarith [hchoices 0]

end EditApproximation

end OAI
