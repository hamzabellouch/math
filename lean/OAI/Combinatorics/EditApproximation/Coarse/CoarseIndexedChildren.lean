import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryEvaluation
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- The executable child loop carries indices and cached subtree lengths.
In particular it never flattens a semantic source tree to obtain its length. -/


theorem coarseIndexChildren_eq {B d : ℕ} {α : Type*} (k q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ) (children : Fin B → CoarseSourceTree B α d)
    (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ)
    (indexed : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (draw : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B d)
    (hw : ∀ i, width i = (children i).word.length)
    (he : ∀ i a start, indexed i a start = evaluate (children i) (below i) a start)
    (allowance : BinaryFraction) (indices : List (Fin B)) (start : ℕ) :
    coarseIndexChildren k q L two width indexed draw allowance indices start =
      coarseBinaryChildren k q L two evaluate allowance
        (indices.map fun i => (children i, draw i, below i)) start := by
  induction indices generalizing start with
  | nil => rfl
  | cons i rest ih =>
    simp only [coarseIndexChildren, List.map_cons, coarseBinaryChildren, he, hw, ih]

end BinaryFraction
end EditApproximation

end OAI
