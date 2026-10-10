import OAI.Combinatorics.TwoWayAutomata.Source
import OAI.Combinatorics.Automata.Model

namespace OAI

namespace TwoWayComplementation.CompanionBridge

open OneWayLiveness
open scoped SetRel

/-- Exact currying/uncurrying equivalence of the two full relation alphabets. -/
def relationEquiv (H : Type*) : BRel H ≃ SetRel H H where
  toFun R := {xy | R.holds xy.1 xy.2}
  invFun R := ⟨fun x y => (x, y) ∈ R⟩
  left_inv _R := rfl
  right_inv _R := rfl

/-- Both products compose in path order, including the identity for the empty word. -/
theorem relationProduct_map {H : Type*} (w : List (BRel H)) :
    relationProduct (w.map (relationEquiv H)) = relationEquiv H w.prod := by
  induction w with
  | nil => rfl
  | cons R w ih =>
    change relationEquiv H R ○ relationProduct (w.map (relationEquiv H)) =
      relationEquiv H (R * w.prod)
    rw [ih]
    rfl

theorem sourceLanguage_map_iff {H : Type*} (w : List (BRel H)) :
    w.map (relationEquiv H) ∈ sourceLanguage H ↔ BRel.live w := by
  change (relationProduct (w.map (relationEquiv H))).Nonempty ↔ _
  rw [relationProduct_map]
  exact ⟨fun ⟨⟨x, y⟩, h⟩ => ⟨x, y, h⟩, fun ⟨x, y, h⟩ => ⟨(x, y), h⟩⟩

end TwoWayComplementation.CompanionBridge

end OAI
