import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ForestTraversal
open Classical SimpleGraph
noncomputable section
variable {V : Type*} {G : SimpleGraph V}

lemma walk_between_support {s t u v : V} (p : G.Walk s t)
    (hu : u ∈ p.support) (hv : v ∈ p.support) :
    ∃ q : G.Walk u v,q.length ≤ p.length := by
  obtain ⟨p₁,p₂,hp⟩ := Walk.mem_support_iff_exists_append.mp hu
  have hlen : p₁.length+p₂.length=p.length := by rw [hp,Walk.length_append]
  rw [hp,Walk.mem_support_append_iff] at hv
  rcases hv with hv | hv
  · refine ⟨(p₁.dropUntil v hv).reverse,?_⟩
    rw [Walk.length_reverse,Walk.length_dropUntil]
    omega
  · refine ⟨p₂.takeUntil v hv,?_⟩
    exact (Walk.length_le_of_isSubwalk (p₂.isSubwalk_takeUntil hv)).trans (by omega)

end
end OrdinaryCorrelations.ForestTraversal

end

end OAI
