import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import OAI.Computability.PerfectCompleteness.Reduction.Target

namespace OAI

section

namespace PerfectCompleteness

private theorem fiber_card_eq_filter_length {n : Nat} (p : Fin n → Prop)
    [DecidablePred p] :
    Fintype.card {a : Fin n // p a} =
      ((List.finRange n).filter (fun a => decide (p a))).length := by
  rw [Fintype.card_of_subtype
    (((List.finRange n).filter (fun a => decide (p a))).toFinset)
    (by intro a; simp)]
  exact List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)

theorem ProjectionTable.fiber_card {q : Nat} (table : ProjectionTable q) (b : Fin q) :
    Fintype.card {a : Fin (2 * q) // table.images[a] = b} = 2 := by
  rw [fiber_card_eq_filter_length]
  exact table.exactlyTwo b

def ProjectionTable.ofMap {q : Nat} (p : Fin (2 * q) → Fin q)
    (h : ∀ b, Fintype.card {a : Fin (2 * q) // p a = b} = 2) : ProjectionTable q where
  images := Vector.ofFn p
  exactlyTwo b := by
    simpa [fiber_card_eq_filter_length] using h b

@[simp] theorem ProjectionTable.ofMap_apply {q : Nat} (p : Fin (2 * q) → Fin q)
    (h : ∀ b, Fintype.card {a : Fin (2 * q) // p a = b} = 2) (a : Fin (2 * q)) :
    (ProjectionTable.ofMap p h).images[a] = p a := by
  simp [ProjectionTable.ofMap]

end PerfectCompleteness

end

end OAI
