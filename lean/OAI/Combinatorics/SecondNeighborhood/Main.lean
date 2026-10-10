import OAI.Combinatorics.SecondNeighborhood.Reduction
import OAI.Combinatorics.SecondNeighborhood.Pruning
import OAI.Combinatorics.SecondNeighborhood.ExtremalContradiction

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem exists_goodVertex (r : V → V → Prop) (hr : IsOriented r) :
    ∃ v, GoodVertex r v := by
  classical
  by_contra h
  have hcounter : Counterexample r := (counterexample_iff_not_conjecture r).mpr h
  obtain ⟨n, hn, g, hg, hpos, hgrowth⟩ := counterexample_reduction hr hcounter
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Extremal.no_strictSubsetGrowth_of_pruning hg hpos (Pruning.pruning g) hgrowth

end SeymourSecondNeighborhood

end OAI
