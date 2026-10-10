import Mathlib
import OAI.Geometry.HyperbolicGroups.TreeCentroidCut

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
variable {V : Type*} [DecidableEq V]

lemma tree_closer_neighbor_mem_path {G : SimpleGraph V} (hG : G.IsTree)
    {r v w : V} (p : G.Walk r v) (hp : p.IsPath) (hadj : G.Adj v w)
    (hd : G.dist r w < G.dist r v) : w ∈ p.support := by
  by_contra hw
  obtain ⟨q,hq,hql⟩ := hG.connected.exists_path_of_dist r w
  have hv := hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp hadj.symm hw
  have heq := hG.isAcyclic.path_concat hp hq hadj hv
  have hpl := tree_path_length_eq_dist hG p hp
  rw [heq,Walk.length_concat,hpl] at hql
  omega

lemma tree_closer_neighbor_unique {G : SimpleGraph V} (hG : G.IsTree)
    {r v a b : V} (ha : G.Adj v a) (hb : G.Adj v b)
    (hda : G.dist r a < G.dist r v) (hdb : G.dist r b < G.dist r v) : a = b := by
  obtain ⟨p,hp,_⟩ := hG.connected.exists_path_of_dist r v
  exact (hG.isAcyclic.eq_penultimate_of_adj_end hp ha
    (tree_closer_neighbor_mem_path hG p hp ha hda)).trans
      (hG.isAcyclic.eq_penultimate_of_adj_end hp hb
        (tree_closer_neighbor_mem_path hG p hp hb hdb)).symm

/-- Root closure is the exact property satisfied by a union of root paths.
It says every predecessor of a protected vertex is protected. -/
def RootClosed (G : SimpleGraph V) (root : V) (S : Set V) : Prop :=
  ∀ v ∈ S, ∀ w, G.Adj v w → G.dist root w < G.dist root v → w ∈ S

variable [Fintype V]

/-- Any finite boundary supported on a tree must lie in a root-closed hull
of its possible ends. The hypothesis outside the hull asks for two DISTINCT
boundary neighbors; the proof uses a furthest unprotected boundary vertex.
This is a tree theorem, not a planar separator assumed by an interface. -/
theorem tree_boundary_in_hull {G : SimpleGraph V} (hG : G.IsTree)
    (root : V) (S : Set V) (hS : RootClosed G root S) (B : V → Prop)
    (hB : ∀ v, B v → v ∉ S → ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b ∧ B a ∧ B b) :
    ∀ v, B v → v ∈ S := by
  classical
  by_contra h
  push Not at h
  obtain ⟨v,hv,hvS⟩ := h
  let U := Finset.univ.filter (fun x => B x ∧ x ∉ S)
  have hU : U.Nonempty := ⟨v,by simp only [U,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hv,hvS⟩⟩
  obtain ⟨x,hx,hmax⟩ := Finset.exists_max_image U (G.dist root) hU
  have hxB : B x ∧ x ∉ S := by simpa only [U,Finset.mem_filter,Finset.mem_univ,true_and] using hx
  obtain ⟨a,b,hab,ha,hb,haB,hbB⟩ := hB x hxB.1 hxB.2
  have hdown : ∀ y, G.Adj x y → B y → G.dist root y < G.dist root x := by
    intro y hxy hyB
    rcases hG.dist_eq_dist_add_one_of_adj root hxy with hd | hd
    · omega
    · have hyS : y ∉ S := by
        intro hy
        exact hxB.2 (hS y hy x hxy.symm (by omega))
      have hyU : y ∈ U := by
        simp only [U,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨hyB,hyS⟩
      have hm := hmax y hyU
      omega
  exact hab (tree_closer_neighbor_unique hG ha hb (hdown a ha haB) (hdown b hb hbB))

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
