import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ : Type*} (G : BondGraph V E) [Group Λ] [MulAction Λ V]
variable (α : Λ → G.Aut) (hα : ∀ g x, (α g).vertex x=g • x)

include α hα in
lemma action_orbit_dense (hc : G.fullGraph.Connected) (S : Set V) (hS : S.Finite)
    (hcover : ∀ x, ∃ s∈S, ∃ g : Λ, g • s=x) (o : V) :
    ∃ c : ℕ, ∀ y, ∃ g : Λ, g • o∈G.vertexBall y c := by
  obtain ⟨c,hc'⟩ := G.finite_subset_vertexBall hc o hS
  refine ⟨c,?_⟩
  intro y
  obtain ⟨s,hs,g,rfl⟩ := hcover y
  refine ⟨g,?_⟩
  rw [←hα g o,←hα g s,Aut.vertexBall_mem]
  exact G.vertexBall_comm.mp (hc' hs)

end CriticalPercolation.BondGraph
end
end
end

end OAI
