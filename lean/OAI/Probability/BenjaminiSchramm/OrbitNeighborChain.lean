import OAI.Probability.BenjaminiSchramm.FiniteOrbitStationary
import OAI.Probability.BenjaminiSchramm.OrbitHeightComparison

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

abbrev VertexOrbit := MulAction.orbitRel.Quotient G.Aut V

def vertexOrbit (x : V) : G.VertexOrbit := Quotient.mk'' x

@[simp] lemma vertexOrbit_aut (φ : G.Aut) (x : V) :
    G.vertexOrbit (φ.vertex x) = G.vertexOrbit x :=
  Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨φ,rfl⟩)

lemma orbit_out_aut (x : V) : ∃ φ : G.Aut, φ.vertex (G.vertexOrbit x).out = x := by
  have he : (Quotient.mk'' (G.vertexOrbit x).out : G.VertexOrbit) = Quotient.mk'' x :=
    (G.vertexOrbit x).out_eq'
  exact MulAction.mem_orbit_iff.mp (MulAction.mem_orbit_symm.mp (Quotient.exact he))

def modularWalkDegree (x : V) : ℕ := (G.fullGraph.neighborSet x).ncard

lemma modularWalkDegree_pos [Nontrivial V] (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x : V) : 0 < G.modularWalkDegree x := by
  apply (Set.ncard_pos (G.finite_neighbors hl x)).mpr
  have h := hc.preconnected.not_isIsolated x
  unfold SimpleGraph.IsIsolated at h
  push Not at h
  exact h

lemma modularWalkDegree_aut (φ : G.Aut) (x : V) :
    G.modularWalkDegree (φ.vertex x) = G.modularWalkDegree x := by
  have he : φ.vertex '' G.fullGraph.neighborSet x = G.fullGraph.neighborSet (φ.vertex x) := by
    ext y
    obtain ⟨z,rfl⟩ := φ.vertex.surjective y
    simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right,SimpleGraph.mem_neighborSet,
      Aut.fullGraph_adj]
  unfold modularWalkDegree
  rw [← he,Set.ncard_image_of_injective _ φ.vertex.injective]

def orbitNeighborCount (hl : G.LocallyFinite) (i j : G.VertexOrbit) : ℕ :=
  (((G.finite_neighbors hl i.out).toFinset).filter fun y => G.vertexOrbit y = j).card

def orbitWalkKernel (hl : G.LocallyFinite) (i j : G.VertexOrbit) : ℝ :=
  G.orbitNeighborCount hl i j / (G.modularWalkDegree i.out : ℝ)

lemma orbitWalkKernel_nonneg (hl : G.LocallyFinite) (i j : G.VertexOrbit) :
    0 ≤ G.orbitWalkKernel hl i j := by
  unfold orbitWalkKernel
  positivity

lemma orbitNeighborCount_sum [Fintype G.VertexOrbit] (hl : G.LocallyFinite) (i : G.VertexOrbit) :
    ∑ j, G.orbitNeighborCount hl i j = G.modularWalkDegree i.out := by
  have he := Finset.card_eq_sum_card_fiberwise
    (s := (G.finite_neighbors hl i.out).toFinset) (t := Finset.univ)
    (f := G.vertexOrbit) (by intro x _; exact Finset.mem_univ _)
  simpa only [orbitNeighborCount,modularWalkDegree,
    Set.ncard_eq_toFinset_card _ (G.finite_neighbors hl i.out)] using he.symm

lemma orbitWalkKernel_row_sum [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (i : G.VertexOrbit) :
    ∑ j, G.orbitWalkKernel hl i j = 1 := by
  simp only [orbitWalkKernel,← Finset.sum_div,← Nat.cast_sum,G.orbitNeighborCount_sum hl]
  exact div_self (Nat.cast_ne_zero.mpr (G.modularWalkDegree_pos hc hl i.out).ne')

lemma orbitWalkKernel_pos_of_adj [Nontrivial V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) {x y : V} (hxy : G.fullGraph.Adj x y) :
    0 < G.orbitWalkKernel hl (G.vertexOrbit x) (G.vertexOrbit y) := by
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut x
  have hy : φ.vertex.symm y ∈ G.fullGraph.neighborSet (G.vertexOrbit x).out := by
    have h := (Aut.fullGraph_adj G φ (G.vertexOrbit x).out (φ.vertex.symm y)).mp
      (by simpa only [hφ,Equiv.apply_symm_apply] using hxy)
    exact h
  have ho : G.vertexOrbit (φ.vertex.symm y) = G.vertexOrbit y := by
    simpa only [Equiv.apply_symm_apply] using (G.vertexOrbit_aut φ (φ.vertex.symm y)).symm
  unfold orbitWalkKernel
  apply div_pos _ (Nat.cast_pos.mpr (G.modularWalkDegree_pos hc hl _))
  apply Nat.cast_pos.mpr
  apply Finset.card_pos.mpr
  exact ⟨φ.vertex.symm y,Finset.mem_filter.mpr ⟨(G.finite_neighbors hl _).mem_toFinset.mpr hy,ho⟩⟩

lemma orbitWalkKernel_irreducible [Nontrivial V] (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (i j : G.VertexOrbit) :
    Relation.ReflTransGen (fun u v => 0 < G.orbitWalkKernel hl u v) i j := by
  have hpath := (G.fullGraph.reachable_iff_reflTransGen i.out j.out).mp (hc i.out j.out)
  have hm : Relation.ReflTransGen (fun u v => 0 < G.orbitWalkKernel hl u v)
      (G.vertexOrbit i.out) (G.vertexOrbit j.out) :=
    hpath.head_induction_on (Relation.ReflTransGen.refl) fun h _ ih =>
      (Relation.ReflTransGen.single
        (r := fun u v : G.VertexOrbit => 0 < G.orbitWalkKernel hl u v)
        (G.orbitWalkKernel_pos_of_adj hc hl h)).trans ih
  simpa only [vertexOrbit,Quotient.out_eq'] using hm

theorem exists_positive_orbit_stationary [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) :
    ∃ μ : G.VertexOrbit → ℝ, (∀ i, 0 < μ i) ∧
      (∑ i, μ i = 1) ∧ orbitChainStep (G.orbitWalkKernel hl) μ = μ := by
  let : Nonempty G.VertexOrbit := ⟨G.vertexOrbit (Classical.arbitrary V)⟩
  exact finite_orbit_stationary_positive (G.orbitWalkKernel hl)
    (G.orbitWalkKernel_nonneg hl) (G.orbitWalkKernel_row_sum hc hl)
    (G.orbitWalkKernel_irreducible hc hl)

end CriticalPercolation.BondGraph

end

end OAI
