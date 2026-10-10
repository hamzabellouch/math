import OAI.Probability.BenjaminiSchramm.OrbitNeighborChain

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stationaryOrbitWeight (μ : G.VertexOrbit → ℝ) (x : V) : ℝ :=
  μ (G.vertexOrbit x) / G.modularWalkDegree x

lemma stationaryOrbitWeight_pos [Nontrivial V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i) (x : V) :
    0 < G.stationaryOrbitWeight μ x :=
  div_pos (hμ _) (Nat.cast_pos.mpr (G.modularWalkDegree_pos hc hl x))

lemma stationaryOrbitWeight_aut (μ : G.VertexOrbit → ℝ) (φ : G.Aut) (x : V) :
    G.stationaryOrbitWeight μ (φ.vertex x) = G.stationaryOrbitWeight μ x := by
  simp only [stationaryOrbitWeight,G.vertexOrbit_aut,G.modularWalkDegree_aut]

lemma stationaryOrbitWeight_out (μ : G.VertexOrbit → ℝ) (x : V) :
    G.stationaryOrbitWeight μ x = G.stationaryOrbitWeight μ (G.vertexOrbit x).out := by
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut x
  simpa only [hφ] using G.stationaryOrbitWeight_aut μ φ (G.vertexOrbit x).out

theorem stationaryOrbitWeight_uniform_bounds [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x, m ≤ G.stationaryOrbitWeight μ x ∧
      G.stationaryOrbitWeight μ x ≤ M := by
  let : Nonempty G.VertexOrbit := ⟨G.vertexOrbit (Classical.arbitrary V)⟩
  let w : G.VertexOrbit → ℝ := fun i => G.stationaryOrbitWeight μ i.out
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ
    (show G.VertexOrbit → OrderDual ℝ from w) Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  refine ⟨w i,w j,G.stationaryOrbitWeight_pos hc hl μ hμ i.out,fun x => ?_⟩
  rw [G.stationaryOrbitWeight_out μ x]
  exact ⟨hi (G.vertexOrbit x) (Finset.mem_univ _),hj (G.vertexOrbit x) (Finset.mem_univ _)⟩

theorem stationaryOrbitHeight_uniform_comparison [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y-G.modularLogHeight x y| ≤ D := by
  obtain ⟨m,M,hm,ha⟩ := G.stationaryOrbitWeight_uniform_bounds hc hl μ hμ
  refine ⟨Real.log M-Real.log m,?_,fun x y => G.orbitAdjustedHeight_sub_bound _ m M hm ha x y⟩
  have hx := ha (Classical.arbitrary V)
  exact sub_nonneg.mpr (Real.log_le_log hm (hx.1.trans hx.2))

end CriticalPercolation.BondGraph

end

end OAI
