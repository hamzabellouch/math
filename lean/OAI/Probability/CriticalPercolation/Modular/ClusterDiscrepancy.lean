import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.Link
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphInsert
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph

variable {V E : Type*} [Fintype V] (G : BondGraph V E)

noncomputable def clusterSize (ω : Set E) (v : V) : ℕ :=
  (G.cluster ω v).toFinset.card

omit [Fintype V] in
lemma cluster_eq_of_reachable {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : G.cluster ω u = G.cluster ω v := by
  ext z
  exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

omit [Fintype V] in
lemma cluster_disjoint_of_not_reachable {ω : Set E} {u v : V}
    (h : ¬ (G.openGraph ω).Reachable u v) : Disjoint (G.cluster ω u) (G.cluster ω v) := by
  apply Set.disjoint_left.mpr
  intro z hu hv
  exact h (hu.trans hv.symm)

lemma clusterSize_pos (ω : Set E) (v : V) : 0 < G.clusterSize ω v := by
  apply Finset.card_pos.mpr
  exact ⟨v, Set.mem_toFinset.mpr (SimpleGraph.Reachable.refl _)⟩

lemma clusterSize_eq_of_reachable {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : G.clusterSize ω u = G.clusterSize ω v := by
  unfold clusterSize
  rw [G.cluster_eq_of_reachable h]

noncomputable def rootMass (f : ℕ → ℝ) (ω : Set E) (v : V) : ℝ :=
  f (G.clusterSize ω v) / G.clusterSize ω v

lemma sum_rootMass_cluster (f : ℕ → ℝ) (ω : Set E) (u : V) :
    (∑ v, if (G.openGraph ω).Reachable u v then G.rootMass f ω v else 0) =
      f (G.clusterSize ω u) := by
  have he : (fun v => if (G.openGraph ω).Reachable u v then G.rootMass f ω v else 0) =
      (fun v => if v ∈ G.cluster ω u then G.rootMass f ω u else 0) := by
    funext v
    by_cases hv : (G.openGraph ω).Reachable u v
    · simp only [cluster, Set.mem_ofPred_eq, hv,ite_true,rootMass,
        G.clusterSize_eq_of_reachable hv]
    · simp [cluster,hv]
  rw [he,Finset.sum_ite]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_zero,add_zero]
  have hfilter : Finset.univ.filter (fun v => v ∈ G.cluster ω u) = (G.cluster ω u).toFinset := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_toFinset]
  rw [hfilter]
  change (G.clusterSize ω u : ℝ) * (f (G.clusterSize ω u) / G.clusterSize ω u) = _
  field_simp [show (G.clusterSize ω u : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (G.clusterSize_pos ω u).ne']

omit [Fintype V] in
lemma incident_cluster_iff (ω : Set E) (e : E) (x y : V) (he : G.ends e = s(x,y)) (v : V) :
    e ∈ G.incidentEdges (G.cluster ω v) ↔
      (G.openGraph ω).Reachable x v ∨ (G.openGraph ω).Reachable y v := by
  constructor
  · rintro ⟨z,hz,hze⟩
    rw [he] at hze
    rcases (by simpa using hze : z=x ∨ z=y) with rfl|rfl
    · exact Or.inl hz.symm
    · exact Or.inr hz.symm
  · rintro (hx|hy)
    · exact ⟨x,hx.symm,by simp [he]⟩
    · exact ⟨y,hy.symm,by simp [he]⟩

lemma sum_incident_rootMass (f : ℕ → ℝ) (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) :
    (∑ v, if e ∈ G.incidentEdges (G.cluster ω v) then G.rootMass f ω v else 0) =
      f (G.clusterSize ω x) + if (G.openGraph ω).Reachable x y then 0 else f (G.clusterSize ω y) := by
  simp_rw [G.incident_cluster_iff ω e x y he]
  by_cases hxy : (G.openGraph ω).Reachable x y
  · have hi : ∀ v, ((G.openGraph ω).Reachable x v ∨ (G.openGraph ω).Reachable y v) ↔
          (G.openGraph ω).Reachable x v := fun v =>
        ⟨fun h => h.elim id (fun hy => hxy.trans hy), Or.inl⟩
    simp_rw [hi]
    rw [G.sum_rootMass_cluster,ite_eq_left hxy,add_zero]
  · have hi : ∀ v, (if (G.openGraph ω).Reachable x v ∨ (G.openGraph ω).Reachable y v
          then G.rootMass f ω v else 0) =
        (if (G.openGraph ω).Reachable x v then G.rootMass f ω v else 0) +
        (if (G.openGraph ω).Reachable y v then G.rootMass f ω v else 0) := by
      intro v
      by_cases hx : (G.openGraph ω).Reachable x v <;>
        by_cases hy : (G.openGraph ω).Reachable y v <;> simp [hx,hy]
      exact (hxy (hx.trans hy.symm)).elim
    simp_rw [hi]
    rw [Finset.sum_add_distrib,G.sum_rootMass_cluster,G.sum_rootMass_cluster,ite_eq_right hxy]

omit [Fintype V] in
lemma cluster_insert_endpoint (ω : Set E) (e : E) (x y : V) (he : G.ends e = s(x,y)) :
    G.cluster (insert e ω) x = G.cluster ω x ∪ G.cluster ω y := by
  ext v
  simp only [cluster,Set.mem_ofPred_eq,Set.mem_union,G.openGraph_insert ω e x y he,
    Wiring.reachable_sup_edge]
  constructor
  · rintro (h|⟨_,h⟩|⟨_,h⟩)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _,h⟩)

lemma clusterSize_insert_of_disconnected (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) (hxy : ¬ (G.openGraph ω).Reachable x y) :
    G.clusterSize (insert e ω) x = G.clusterSize ω x + G.clusterSize ω y := by
  unfold clusterSize
  rw [G.cluster_insert_endpoint ω e x y he,Set.toFinset_union,Finset.card_union_of_disjoint]
  exact Set.disjoint_toFinset.mpr (G.cluster_disjoint_of_not_reachable hxy)

lemma clusterSize_insert_of_connected (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) (hxy : (G.openGraph ω).Reachable x y) :
    G.clusterSize (insert e ω) x = G.clusterSize ω x := by
  unfold clusterSize
  rw [G.cluster_insert_endpoint ω e x y he,G.cluster_eq_of_reachable hxy,Set.union_self]

end CriticalPercolation.BondGraph
end
end
end

end OAI
