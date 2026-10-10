import Mathlib
import OAI.Geometry.HyperbolicGroups.TreeCentroid

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open Finset SimpleGraph
variable {V : Type*}

lemma tree_path_length_eq_dist {G : SimpleGraph V} (hG : G.IsTree) {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) : p.length = G.dist x y := by
  obtain ⟨q,hq,hql⟩ := hG.connected.exists_path_of_dist x y
  have heq := hG.isAcyclic.subsingleton_path x y |>.elim ⟨p,hp⟩ ⟨q,hq⟩
  have hwalk : p = q := congrArg Subtype.val heq
  rwa [hwalk]

variable [Fintype V] [DecidableEq V]

lemma treeBranch_of_avoiding_walk {G : SimpleGraph V} (hG : G.IsTree) {v w x : V}
    (hadj : G.Adj v w) (p : G.Walk x w) (havoid : v ∉ p.support) :
    x ∈ treeBranch G v w := by
  let q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  have hv : v ∉ q.support := fun h => havoid (p.support_bypass_subset_support h)
  obtain ⟨r,hr,hrl⟩ := hG.connected.exists_path_of_dist x v
  have hw : w ∈ r.support :=
    hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hr hq hadj hv
  have hid := hG.isAcyclic.path_concat hq hr hadj.symm hw
  have hql := tree_path_length_eq_dist hG q hq
  rw [hid,Walk.length_concat,hql] at hrl
  simp only [treeBranch,Finset.mem_filter,Finset.mem_univ,true_and]
  omega

/-- The weighted centroid really separates the tree: every connected set
remaining after removing it has at most half the total weight. All weights
are on actual vertices and no combinatorial separation is hypothesized. -/
theorem weighted_tree_vertex_separator (G : SimpleGraph V) (hG : G.IsTree)
    (weight : V → ℝ) (hw : ∀ x, 0 ≤ weight x) :
    ∃ v : V, ∀ S : Finset V, v ∉ S → (G.induce (S : Set V)).Preconnected →
      2 * ∑ x ∈ S, weight x ≤ ∑ x : V, weight x := by
  obtain ⟨v,hv⟩ := weighted_tree_centroid G hG weight
  refine ⟨v,?_⟩
  intro S hvS hconn
  by_cases hS : S.Nonempty
  · obtain ⟨x,hx⟩ := hS
    obtain ⟨p,hp,_⟩ := hG.connected.exists_path_of_dist v x
    cases p with
    | nil => exact (hvS hx).elim
    | @cons v w x hadj q =>
      have havoid : v ∉ q.support := by
        have hnodup := hp.support_nodup
        exact (List.nodup_cons.mp (by simpa only [Walk.support_cons] using hnodup)).1
      have hsub : S ⊆ treeBranch G v w := by
        intro y hy
        obtain ⟨r⟩ := hconn ⟨y,hy⟩ ⟨x,hx⟩
        let r' := r.map (SimpleGraph.Embedding.induce (S : Set V)).toHom
        have hr' : v ∉ r'.support := by
          intro h
          rw [Walk.support_map] at h
          obtain ⟨z,_,hz⟩ := List.mem_map.mp h
          exact hvS (hz ▸ z.property)
        apply treeBranch_of_avoiding_walk hG hadj (r'.append q.reverse)
        intro h
        have hh := (Walk.mem_support_append_iff r' q.reverse).mp h
        rcases hh with hh | hh
        · exact hr' hh
        · exact havoid (by simpa using hh)
      exact le_trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hw x)) (by norm_num)) (hv w hadj)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.sum_empty,mul_zero]
    exact Finset.sum_nonneg (fun x _ => hw x)

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
