import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

lemma sum_comp_le_fibre_bound {α β : Type*} (S : Finset α) (T : Finset β)
    (g : α → β) (f : β → ℝ) (L : ℕ) (hf : ∀ b, 0≤f b)
    (hmap : ∀ a∈S, g a∈T) (hL : ∀ b, (S.filter (fun a => g a=b)).card≤L) :
    ∑ a∈S, f (g a) ≤ (L:ℝ)*∑ b∈T, f b := by
  rw [Finset.sum_comp]
  calc
    _ ≤ ∑ b∈S.image g, (L:ℝ)*f b := by
      apply Finset.sum_le_sum
      intro b _
      simp only [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hL b)) (hf b)
    _ ≤ ∑ b∈T, (L:ℝ)*f b := Finset.sum_le_sum_of_subset_of_nonneg
      (by rintro b hb; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb; exact hmap a ha)
      (fun b _ _ => mul_nonneg (Nat.cast_nonneg _) (hf b))
    _ = _ := (Finset.mul_sum _ _ _).symm

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma finite_bond_endpoints {K : Set E} (hK : K.Finite) :
    (⋃ e∈K, {v | v∈G.ends e}).Finite := by
  apply hK.biUnion
  intro e _
  convert (G.ends e).toFinset.finite_toSet using 1
  ext v
  exact Sym2.mem_toFinset.symm

lemma finite_bonds_in_ball (hconnected : G.fullGraph.Connected) (o : V)
    {K : Set E} (hK : K.Finite) : ∃ W, K ⊆ G.inducedEdges (G.vertexBall o W) := by
  obtain ⟨W,hW⟩ := G.finite_subset_vertexBall hconnected o (G.finite_bond_endpoints hK)
  refine ⟨W,?_⟩
  intro e he v hv
  exact hW (Set.mem_iUnion₂.mpr ⟨e,he,hv⟩)

lemma inducedEdges_monotone : Monotone G.inducedEdges := by
  intro S T h e he v hv
  exact h (he v hv)

def inducedBallExhaustion (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (o : V) : Set.FiniteExhaustion (Set.univ : Set E) where
  toFun n := G.inducedEdges (G.vertexBall o n)
  finite' n := G.finite_inducedEdges hlocal (G.vertexBall_finite hlocal o n)
  subset_succ' n := G.inducedEdges_monotone (G.vertexBall_mono o (Nat.le_succ n))
  iUnion_eq' := by
    apply Set.eq_univ_of_forall
    intro e
    obtain ⟨W,hW⟩ := G.finite_bonds_in_ball hconnected o (Set.finite_singleton e)
    exact Set.mem_iUnion.mpr ⟨W,hW rfl⟩

lemma Aut.inducedEdges_map (φ : G.Aut) {K : Set E} {S : Set V}
    (hKS : K⊆G.inducedEdges S) : φ.edge '' K ⊆ G.inducedEdges (φ.vertex '' S) := by
  rintro e ⟨a,ha,rfl⟩ v hv
  rw [φ.preserves] at hv
  obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
  exact ⟨w,hKS ha w hw,rfl⟩

lemma translated_bonds_in_ball (o u v : V) (n C W : ℕ) (φ : G.Aut)
    (hv : v∈G.vertexBall o n) (hφ : φ.vertex u ∈ G.vertexBall v C)
    {K : Set E} (hK : K⊆G.inducedEdges (G.vertexBall u W)) :
    φ.edge '' K ⊆ G.inducedEdges (G.vertexBall o (n+C+W)) := by
  apply (Aut.inducedEdges_map G φ hK).trans
  apply G.inducedEdges_monotone
  rw [Aut.vertexBall_image]
  exact G.vertexBall_add (G.vertexBall_add hv C hφ) W

lemma orbit_edge_fibre_bound (hlocal : G.LocallyFinite) (C M : ℕ)
    (hM : ∀ v, (G.vertexBall v C).ncard≤M) (u : V) (e : E) (hu : u∈G.ends e)
    (φ : V → G.Aut) (hφ : ∀ v, (φ v).vertex u ∈ G.vertexBall v C)
    (S : Finset V) (f : E) : (S.filter (fun v => (φ v).edge e=f)).card ≤ 2*M := by
  have hsub : (↑(S.filter (fun v => (φ v).edge e=f)) : Set V) ⊆
      G.vertexBall (G.ends f).out.1 C ∪ G.vertexBall (G.ends f).out.2 C := by
    intro v hv
    have he : (φ v).edge e=f := (Finset.mem_filter.mp hv).2
    have hm : (φ v).vertex u ∈ G.ends f := by
      rw [← he,(φ v).preserves]
      exact Sym2.mem_map.mpr ⟨u,hu,rfl⟩
    rw [(G.ends f).out_eq.symm,Sym2.mem_iff] at hm
    have hd := (G.vertexBall_comm).mp (hφ v)
    exact hm.elim (fun h => Or.inl (h ▸ hd)) (fun h => Or.inr (h ▸ hd))
  have hc := Set.ncard_le_ncard hsub
    ((G.vertexBall_finite hlocal _ C).union (G.vertexBall_finite hlocal _ C))
  simp only [Set.ncard_coe_finset] at hc
  have hh := Set.ncard_union_le (G.vertexBall (G.ends f).out.1 C)
    (G.vertexBall (G.ends f).out.2 C)
  exact hc.trans (hh.trans (by have h1 := hM (G.ends f).out.1; have h2 := hM (G.ends f).out.2; omega))

end BondGraph
end CriticalPercolation
end
end
end

end OAI
