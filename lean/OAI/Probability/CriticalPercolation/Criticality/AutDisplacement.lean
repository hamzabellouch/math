import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.BallIncidence
import OAI.Probability.CriticalPercolation.Gluing.OpenTrialBound

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma aut_moves_vertex_outside_ball [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (R : ℕ) :
    ∃ φ : G.Aut, φ.vertex o ∉ G.vertexBall o R := by
  obtain ⟨C,hC⟩ := G.orbit_density_radius hc hq o
  obtain ⟨v,hv⟩ := (G.vertexBall_finite hl o (R+C)).exists_notMem
  obtain ⟨φ,hφ⟩ := hC v
  refine ⟨φ,fun h => hv ?_⟩
  exact G.vertexBall_add h C (G.vertexBall_comm.mp hφ)

lemma aut_displaces_finite_bonds [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (S : Set E) (hS : S.Finite) :
    ∃ φ : G.Aut, Disjoint S (φ.edge '' S) := by
  obtain ⟨o⟩ := hc.nonempty
  obtain ⟨R,hR⟩ := G.finite_bonds_in_ball hc o hS
  obtain ⟨φ,hφ⟩ := G.aut_moves_vertex_outside_ball hc hl hq o (R+R)
  refine ⟨φ,(G.inducedEdges_disjoint (G.vertexBalls_disjoint hφ)).mono hR ?_⟩
  have hm := Aut.inducedEdges_map G φ hR
  rwa [Aut.vertexBall_image] at hm

end CriticalPercolation.BondGraph
end
end

end OAI
