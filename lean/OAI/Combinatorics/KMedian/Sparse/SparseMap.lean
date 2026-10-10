import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseIntegerLaw

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
variable {α β : Type}

def map (μ : SparseIntegerLaw α) (f : α → β) : SparseIntegerLaw β where
  length := μ.length
  law := μ.law
  states := μ.states.map f

theorem map_moment (μ : SparseIntegerLaw α) (f : α → β) (v : β → ℚ) :
    (μ.map f).moment v=μ.moment (fun a => v (f a)) := by
  unfold moment map
  simp only [Vector.getElem_map]

@[simp] theorem map_states (μ : SparseIntegerLaw α) (f : α → β) (i : Fin (μ.map f).length) :
    (μ.map f).states[i.val]=f μ.states[i.val] := by
  simp only [map,Vector.getElem_map]

end MetricKMedian.SparseIntegerLaw

end OAI
