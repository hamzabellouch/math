import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

protected def Aut.symm (φ : G.Aut) : G.Aut where
  vertex := φ.vertex.symm
  edge := φ.edge.symm
  preserves e := by
    have h := φ.preserves (φ.edge.symm e)
    have hh := congrArg (Sym2.map φ.vertex.symm) h
    simpa only [Equiv.apply_symm_apply,Sym2.map_map,Equiv.symm_comp_self,Sym2.map_id',id_eq] using hh.symm

protected def Aut.trans (φ ψ : G.Aut) : G.Aut where
  vertex := φ.vertex.trans ψ.vertex
  edge := φ.edge.trans ψ.edge
  preserves e := by
    simp only [Equiv.trans_apply,ψ.preserves,φ.preserves,Sym2.map_map]
    rfl

lemma uniform_orbit_density_radius (hconnected : G.fullGraph.Connected)
    (hquasi : G.QuasiTransitive) :
    ∃ C : ℕ, ∀ u v, ∃ φ : G.Aut, φ.vertex u ∈ G.vertexBall v C := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  obtain ⟨o⟩ := hconnected.nonempty
  obtain ⟨R,hR⟩ := G.finite_subset_vertexBall hconnected o hS
  refine ⟨R+R,?_⟩
  intro u v
  obtain ⟨z,hz,φ,hφ⟩ := hcover u
  obtain ⟨w,hw,ψ,hψ⟩ := hcover v
  refine ⟨Aut.trans G (Aut.symm G φ) ψ,?_⟩
  change ψ.vertex (φ.vertex.symm u) ∈ G.vertexBall v (R+R)
  rw [← hφ,Equiv.symm_apply_apply,← hψ,Aut.vertexBall_mem]
  exact G.vertexBall_add ((G.vertexBall_comm).mp (hR hw)) R (hR hz)

lemma vertexBall_ncard_pos (hlocal : G.LocallyFinite) (o : V) (n : ℕ) :
    0 < (G.vertexBall o n).ncard :=
  (Set.ncard_pos (G.vertexBall_finite hlocal o n)).mpr ⟨o,G.mem_vertexBall_self o n⟩

lemma uniform_positive_ball_bound (hquasi : G.QuasiTransitive)
    (n : ℕ) : ∃ M : ℕ, 1≤M ∧ ∀ v, (G.vertexBall v n).ncard ≤ M := by
  obtain ⟨M,hM⟩ := G.uniform_ball_bound hquasi n
  exact ⟨M+1,by omega,fun v => (hM v).trans (Nat.le_succ M)⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
