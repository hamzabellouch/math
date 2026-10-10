import Mathlib

namespace OAI

open scoped Classical

namespace Percolation.BenjaminiSchramm

variable {V : Type*} {H : SimpleGraph V}

def GhostFan (H : SimpleGraph V) (A B : Set V) (x : V) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, ∃ p : H.Walk x a, ∃ q : H.Walk x b, p.edges.Disjoint q.edges

lemma GhostFan.symm {A B : Set V} {x : V} (h : GhostFan H A B x) : GhostFan H B A x := by
  obtain ⟨a,ha,b,hb,p,q,hpq⟩ := h
  exact ⟨b,hb,a,ha,q,p,hpq.symm⟩

lemma walk_edges_disjoint_of_single_support_intersection
    {u v a b z : V} (p : H.Walk u v) (q : H.Walk a b)
    (h : ∀ x ∈ p.support, x ∈ q.support → x = z) : p.edges.Disjoint q.edges := by
  apply List.disjoint_left.mpr
  intro e hp hq
  obtain ⟨⟨c,d⟩,he⟩ := Quot.exists_rep e
  rw [← he] at hp hq
  have hc := h c (p.fst_mem_support_of_mem_edges hp) (q.fst_mem_support_of_mem_edges hq)
  have hd := h d (p.snd_mem_support_of_mem_edges hp) (q.snd_mem_support_of_mem_edges hq)
  exact (p.adj_of_mem_edges hp).ne (hc.trans hd.symm)

lemma ghostFan_of_trail_support {A B : Set V} {a b x : V}
    (ha : a ∈ A) (hb : b ∈ B) (p : H.Walk a b) (hp : p.IsTrail) (hx : x ∈ p.support) :
    GhostFan H A B x := by
  refine ⟨a,ha,b,hb,(p.takeUntil x hx).reverse,p.dropUntil x hx,?_⟩
  simpa only [SimpleGraph.Walk.edges_reverse, List.disjoint_reverse_left] using
    hp.disjoint_edges_takeUntil_dropUntil hx

lemma ghostFan_of_first_arm_support {A B : Set V} {w a b x : V}
    (ha : a ∈ A) (hb : b ∈ B) (p : H.Walk w a) (q : H.Walk w b)
    (hp : p.IsTrail) (hq : q.IsTrail) (hpq : p.edges.Disjoint q.edges) (hx : x ∈ p.support) :
    GhostFan H A B x := by
  apply ghostFan_of_trail_support ha hb (p.reverse.append q)
  · exact (SimpleGraph.Walk.isTrail_append _ _).mpr
      ⟨hp.reverse,hq,by simpa using hpq⟩
  · exact SimpleGraph.Walk.support_subset_support_append_left _ _ (by simpa using hx)

lemma ghostFan_of_arm_avoiding_prefix {A B : Set V} {u w a b v : V}
    (ha : a ∈ A) (hb : b ∈ B) (p : H.Walk w a) (q : H.Walk w b)
    (hpq : p.edges.Disjoint q.edges) (huw : H.Adj u w)
    (hu : u ∉ p.support) (r : H.Walk u v) (hv : v ∈ p.support)
    (hrq : r.edges.Disjoint q.edges)
    (hre : s(u,w) ∉ r.edges) : GhostFan H A B u := by
  refine ⟨a,ha,b,hb,r.append (p.dropUntil v hv),SimpleGraph.Walk.cons huw q,?_⟩
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons]
  apply List.disjoint_left.mpr
  intro e he he'
  rcases List.mem_append.mp he with her | hep
  · rcases List.mem_cons.mp he' with he' | heq
    · exact hre (he' ▸ her)
    · exact List.disjoint_left.mp hrq her heq
  · have hep' := p.edges_dropUntil_subset_edges hv hep
    rcases List.mem_cons.mp he' with he' | heq
    · exact hu (p.fst_mem_support_of_mem_edges (he' ▸ hep'))
    · exact List.disjoint_left.mp hpq hep' heq

lemma GhostFan.of_alternate_walk {A B : Set V} {u w : V}
    (h : GhostFan H A B w) (huw : H.Adj u w)
    (r : H.Walk u w) (hre : s(u,w) ∉ r.edges) : GhostFan H A B u := by
  classical
  obtain ⟨a,ha,b,hb,p₀,q₀,hpq₀⟩ := h
  let p : H.Walk w a := p₀.toPath
  let q : H.Walk w b := q₀.toPath
  have hp : p.IsTrail := p₀.toPath.property.isTrail
  have hq : q.IsTrail := q₀.toPath.property.isTrail
  have hpq : p.edges.Disjoint q.edges := by
    apply List.disjoint_left.mpr
    intro e hep heq
    exact List.disjoint_left.mp hpq₀
      (p₀.edges_toPath_subset_edges hep) (q₀.edges_toPath_subset_edges heq)
  by_cases hu : u ∈ p.support
  · exact ghostFan_of_first_arm_support ha hb p q hp hq hpq hu
  by_cases hu' : u ∈ q.support
  · exact (ghostFan_of_first_arm_support hb ha q p hq hp hpq.symm hu').symm
  let S := p.support.toFinset ∪ q.support.toFinset
  have hwS : w ∈ S := Finset.mem_union_left _ (List.mem_toFinset.mpr p.start_mem_support)
  obtain ⟨v,hv,hvr,hfirst⟩ := r.exists_mem_support_forall_mem_support_imp_eq S
    ⟨w,Finset.mem_filter.mpr ⟨hwS,r.end_mem_support⟩⟩
  let r' := r.takeUntil v hvr
  have hrp : r'.edges.Disjoint p.edges := by
    apply walk_edges_disjoint_of_single_support_intersection r' p
    intro x hxr hxp
    exact hfirst x (Finset.mem_union_left _ (List.mem_toFinset.mpr hxp)) hxr
  have hrq : r'.edges.Disjoint q.edges := by
    apply walk_edges_disjoint_of_single_support_intersection r' q
    intro x hxr hxq
    exact hfirst x (Finset.mem_union_right _ (List.mem_toFinset.mpr hxq)) hxr
  have hre' : s(u,w) ∉ r'.edges := fun he => hre (r.edges_takeUntil_subset_edges hvr he)
  rcases Finset.mem_union.mp hv with hvp | hvq
  · exact ghostFan_of_arm_avoiding_prefix ha hb p q hpq huw hu r'
      (List.mem_toFinset.mp hvp) hrq hre'
  · exact (ghostFan_of_arm_avoiding_prefix hb ha q p hpq.symm huw hu' r'
      (List.mem_toFinset.mp hvq) hrp hre').symm

lemma GhostFan.of_not_isBridge {A B : Set V} {u w : V}
    (h : GhostFan H A B w) (huw : H.Adj u w) (he : ¬H.IsBridge s(u,w)) :
    GhostFan H A B u := by
  obtain ⟨r,hr⟩ := SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp
    (not_not.mp (SimpleGraph.isBridge_iff.not.mp he))
  exact h.of_alternate_walk huw r hr

lemma exists_bridge_to_ghostFan {A B : Set V} {x w : V}
    (r : H.Walk x w) (hw : GhostFan H A B w) (hx : ¬GhostFan H A B x) :
    ∃ u v, H.Adj u v ∧ H.IsBridge s(u,v) ∧
      (H.deleteEdges {s(u,v)}).Reachable x u ∧ GhostFan H A B v ∧ ¬GhostFan H A B u := by
  induction r with
  | nil => exact (hx hw).elim
  | @cons x y w hxy r ih =>
    by_cases hy : GhostFan H A B y
    · have he : H.IsBridge s(x,y) := by
        by_contra hn
        exact hx (hy.of_not_isBridge hxy hn)
      exact ⟨x,y,hxy,he,SimpleGraph.Reachable.refl x,hy,hx⟩
    · obtain ⟨u,v,huv,he,hreach,hv,hu⟩ := ih hw hy
      have hne : s(x,y) ≠ s(u,v) := by
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨hxu,hyv⟩ | ⟨hxv,hyu⟩
        · exact hy (hyv ▸ hv)
        · exact hx (hxv ▸ hv)
      have hxy' : (H.deleteEdges {s(u,v)}).Adj x y := by
        exact SimpleGraph.deleteEdges_adj.mpr ⟨hxy,by simpa using hne⟩
      exact ⟨u,v,huv,he,hxy'.reachable.trans hreach,hv,hu⟩

lemma walk_edges_disjoint_of_bridge {u v a b : V} (he : H.IsBridge s(u,v))
    (p : H.Walk u a) (q : H.Walk v b)
    (hp : s(u,v) ∉ p.edges) (hq : s(u,v) ∉ q.edges) : p.edges.Disjoint q.edges := by
  apply List.disjoint_left.mpr
  intro e hep heq
  obtain ⟨⟨c,d⟩,he'⟩ := Quot.exists_rep e
  rw [← he'] at hep heq
  have hc := p.fst_mem_support_of_mem_edges hep
  have hc' := q.fst_mem_support_of_mem_edges heq
  let r := (p.takeUntil c hc).append (q.takeUntil c hc').reverse
  have hr : s(u,v) ∉ r.edges := by
    simp only [r, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
      List.mem_append, List.mem_reverse, not_or]
    exact ⟨fun h => hp (p.edges_takeUntil_subset_edges hc h),
      fun h => hq (q.edges_takeUntil_subset_edges hc' h)⟩
  exact hr (SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp he r)

lemma bridge_to_ghostFan_avoids_marks {A B : Set V} {u v : V}
    (huv : H.Adj u v) (he : H.IsBridge s(u,v))
    (hv : GhostFan H A B v) (hu : ¬GhostFan H A B u) :
    (∀ a ∈ A, ¬(H.deleteEdges {s(u,v)}).Reachable u a) ∧
    (∀ b ∈ B, ¬(H.deleteEdges {s(u,v)}).Reachable u b) := by
  classical
  suffices h : ∀ (C D : Set V), GhostFan H C D v → ¬GhostFan H C D u →
      ∀ a ∈ C, ¬(H.deleteEdges {s(u,v)}).Reachable u a by
    exact ⟨h A B hv hu,h B A hv.symm (fun hf => hu hf.symm)⟩
  intro C D hv hu a ha hreach
  obtain ⟨a₀,ha₀,b,hb,p₀,q₀,hpq₀⟩ := hv
  let p : H.Walk v a₀ := p₀.toPath
  let q : H.Walk v b := q₀.toPath
  have hpq : p.edges.Disjoint q.edges := by
    apply List.disjoint_left.mpr
    intro e hep heq
    exact List.disjoint_left.mp hpq₀
      (p₀.edges_toPath_subset_edges hep) (q₀.edges_toPath_subset_edges heq)
  have huq : u ∉ q.support := by
    intro h
    exact hu (ghostFan_of_first_arm_support hb ha₀ q p
      q₀.toPath.property.isTrail p₀.toPath.property.isTrail hpq.symm h).symm
  have hqe : s(u,v) ∉ q.edges := fun h => huq (q.fst_mem_support_of_mem_edges h)
  obtain ⟨r,hr⟩ := SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreach
  have hrq := walk_edges_disjoint_of_bridge he r q hr hqe
  apply hu
  refine ⟨a,ha,b,hb,r,SimpleGraph.Walk.cons huv q,?_⟩
  rw [SimpleGraph.Walk.edges_cons]
  apply List.disjoint_left.mpr
  intro e her heq
  rcases List.mem_cons.mp heq with heq | heq
  · exact hr (heq ▸ her)
  · exact List.disjoint_left.mp hrq her heq

lemma GhostFan.mono {K : SimpleGraph V} {A B : Set V} {x : V}
    (h : GhostFan H A B x) (hHK : H ≤ K) : GhostFan K A B x := by
  obtain ⟨a,ha,b,hb,p,q,hpq⟩ := h
  refine ⟨a,ha,b,hb,p.mapLe hHK,q.mapLe hHK,?_⟩
  simpa using hpq

lemma ghostFan_delete_bridge {A B : Set V} {u v : V}
    (hv : GhostFan H A B v) (hu : ¬GhostFan H A B u) :
    GhostFan (H.deleteEdges {s(u,v)}) A B v := by
  classical
  obtain ⟨a,ha,b,hb,p₀,q₀,hpq₀⟩ := hv
  let p : H.Walk v a := p₀.toPath
  let q : H.Walk v b := q₀.toPath
  have hpq : p.edges.Disjoint q.edges := by
    apply List.disjoint_left.mpr
    intro e hep heq
    exact List.disjoint_left.mp hpq₀
      (p₀.edges_toPath_subset_edges hep) (q₀.edges_toPath_subset_edges heq)
  have hup : u ∉ p.support := by
    intro h
    exact hu (ghostFan_of_first_arm_support ha hb p q
      p₀.toPath.property.isTrail q₀.toPath.property.isTrail hpq h)
  have huq : u ∉ q.support := by
    intro h
    exact hu (ghostFan_of_first_arm_support hb ha q p
      q₀.toPath.property.isTrail p₀.toPath.property.isTrail hpq.symm h).symm
  have hpe : s(u,v) ∉ p.edges := fun h => hup (p.fst_mem_support_of_mem_edges h)
  have hqe : s(u,v) ∉ q.edges := fun h => huq (q.fst_mem_support_of_mem_edges h)
  refine ⟨a,ha,b,hb,p.toDeleteEdge s(u,v) hpe,q.toDeleteEdge s(u,v) hqe,?_⟩
  simpa using hpq

lemma two_connections_fan_or_bridge {A B : Set V} {x : V}
    (hA : ∃ a ∈ A, H.Reachable x a) (hB : ∃ b ∈ B, H.Reachable x b) :
    GhostFan H A B x ∨ ∃ u v, H.Adj u v ∧ H.IsBridge s(u,v) ∧
      (H.deleteEdges {s(u,v)}).Reachable x u ∧
      (∀ a ∈ A, ¬(H.deleteEdges {s(u,v)}).Reachable x a) ∧
      (∀ b ∈ B, ¬(H.deleteEdges {s(u,v)}).Reachable x b) ∧
      GhostFan (H.deleteEdges {s(u,v)}) A B v := by
  classical
  by_cases hx : GhostFan H A B x
  · exact Or.inl hx
  right
  obtain ⟨a,ha,⟨p⟩⟩ := hA
  obtain ⟨b,hb,⟨q⟩⟩ := hB
  have haFan : GhostFan H A B a :=
    ⟨a,ha,b,hb,SimpleGraph.Walk.nil,p.reverse.append q,by simp⟩
  obtain ⟨u,v,huv,he,hxu,hv,hu⟩ := exists_bridge_to_ghostFan p haFan hx
  obtain ⟨hA,hB⟩ := bridge_to_ghostFan_avoids_marks huv he hv hu
  exact ⟨u,v,huv,he,hxu,
    fun a ha hxa => hA a ha (hxu.symm.trans hxa),
    fun b hb hxb => hB b hb (hxu.symm.trans hxb),ghostFan_delete_bridge hv hu⟩

end Percolation.BenjaminiSchramm

end OAI
