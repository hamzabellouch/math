import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ConnectedSet

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.Rerooting
open Classical Finset SimpleGraph
noncomputable section
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma walk_support_connected {x y : V} (p : G.Walk x y) : ConnectedSet G p.support.toFinset := by
  intro u hu v hv
  have hu' := List.mem_toFinset.mp hu
  have hv' := List.mem_toFinset.mp hv
  refine ⟨(p.takeUntil u hu').reverse.append (p.takeUntil v hv'),?_⟩
  intro z hz
  apply List.mem_toFinset.mpr
  rw [Walk.mem_support_append_iff] at hz
  rcases hz with hz|hz
  · exact p.support_takeUntil_subset_support hu' (by simpa using hz)
  · exact p.support_takeUntil_subset_support hv' hz
end
end OrdinaryCorrelations.Rerooting

end

end OAI
