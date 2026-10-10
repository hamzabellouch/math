import OAI.Probability.BenjaminiSchramm.GhostFan

namespace OAI

namespace Percolation.BenjaminiSchramm

variable {V : Type*} {H : SimpleGraph V}
attribute [local instance] Classical.decEq

def WalkQuartet (H : SimpleGraph V) (x y z t : V) : Prop :=
  ∃ u v, ∃ p : H.Walk u x, ∃ q : H.Walk u y, ∃ r : H.Walk u v,
    ∃ s : H.Walk v z, ∃ w : H.Walk v t,
      [p.edges,q.edges,r.edges,s.edges,w.edges].Pairwise List.Disjoint

lemma WalkQuartet.swap_left {x y z t : V} (h : WalkQuartet H x y z t) :
    WalkQuartet H y x z t := by
  obtain ⟨u,v,p,q,r,s,w,h⟩ := h
  refine ⟨u,v,q,p,r,s,w,?_⟩
  simp [List.pairwise_cons] at h ⊢
  rcases h with ⟨⟨hpq,hpr,hps,hpw⟩,⟨⟨hqr,hqs,hqw⟩,⟨⟨hrs,hrw⟩,hsw⟩⟩⟩
  exact ⟨⟨hpq.symm,hqr,hqs,hqw⟩,⟨⟨hpr,hps,hpw⟩,⟨⟨hrs,hrw⟩,hsw⟩⟩⟩

lemma WalkQuartet.swap_pairs {x y z t : V} (h : WalkQuartet H x y z t) :
    WalkQuartet H z t x y := by
  obtain ⟨u,v,p,q,r,s,w,h⟩ := h
  refine ⟨v,u,s,w,r.reverse,p,q,?_⟩
  simp [List.pairwise_cons] at h ⊢
  rcases h with ⟨⟨hpq,hpr,hps,hpw⟩,⟨⟨hqr,hqs,hqw⟩,⟨⟨hrs,hrw⟩,hsw⟩⟩⟩
  exact ⟨⟨hsw,hrs.symm,hps.symm,hqs.symm⟩,
    ⟨⟨hrw.symm,hpw.symm,hqw.symm⟩,⟨⟨hpr.symm,hqr.symm⟩,hpq⟩⟩⟩

lemma walk_disjoint_mono {X : Type*} {a b c d : List X}
    (h : a.Disjoint b) (hc : c ⊆ a) (hd : d ⊆ b) : c.Disjoint d := by
  exact List.disjoint_left.mpr (fun _ he hf => List.disjoint_left.mp h (hc he) (hd hf))

lemma quartet_of_split_arm {u x y z t v : V}
    (p : H.Walk u x) (q : H.Walk u y) (r : H.Walk u z)
    (s : H.Walk t v) (hp : p.IsTrail) (hv : v ∈ p.support)
    (hpq : p.edges.Disjoint q.edges) (hpr : p.edges.Disjoint r.edges)
    (hqr : q.edges.Disjoint r.edges) (hsp : s.edges.Disjoint p.edges)
    (hsq : s.edges.Disjoint q.edges) (hsr : s.edges.Disjoint r.edges) :
    WalkQuartet H x t y z := by
  refine ⟨v,u,p.dropUntil v hv,s.reverse,(p.takeUntil v hv).reverse,q,r,?_⟩
  have ha := p.edges_takeUntil_subset_edges hv
  have hb := p.edges_dropUntil_subset_edges hv
  simp [List.pairwise_cons]
  exact ⟨⟨(walk_disjoint_mono hsp (fun _ h => h) hb).symm,
      (hp.disjoint_edges_takeUntil_dropUntil hv).symm,
      walk_disjoint_mono hpq hb (fun _ h => h),
      walk_disjoint_mono hpr hb (fun _ h => h)⟩,
    ⟨⟨walk_disjoint_mono hsp (fun _ h => h) ha,hsq,hsr⟩,
      ⟨⟨walk_disjoint_mono hpq ha (fun _ h => h),
        walk_disjoint_mono hpr ha (fun _ h => h)⟩,hqr⟩⟩⟩

lemma three_walks_from_reachable {x y z : V}
    (hxy : H.Reachable x y) (hxz : H.Reachable x z) :
    ∃ u, ∃ p : H.Walk u x, ∃ q : H.Walk u y, ∃ r : H.Walk u z,
      p.IsTrail ∧ q.IsTrail ∧ r.IsTrail ∧
      p.edges.Disjoint q.edges ∧ p.edges.Disjoint r.edges ∧ q.edges.Disjoint r.edges := by
  classical
  obtain ⟨p₀⟩ := hxy
  let p : H.Walk x y := p₀.toPath
  obtain ⟨r₀⟩ := hxz.symm
  let r : H.Walk z x := r₀.toPath
  let S := p.support.toFinset
  obtain ⟨u,hu,hur,hfirst⟩ := r.exists_mem_support_forall_mem_support_imp_eq S
    ⟨x,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr p.start_mem_support,r.end_mem_support⟩⟩
  have hup : u ∈ p.support := List.mem_toFinset.mp hu
  let a := p.takeUntil u hup
  let b := p.dropUntil u hup
  let c := r.takeUntil u hur
  have hcp : c.edges.Disjoint p.edges := by
    apply walk_edges_disjoint_of_single_support_intersection c p
    intro w hw hpw
    exact hfirst w (List.mem_toFinset.mpr hpw) hw
  refine ⟨u,a.reverse,b,c.reverse,
    (p₀.toPath.property.isTrail.takeUntil hup).reverse,
    p₀.toPath.property.isTrail.dropUntil hup,
    (r₀.toPath.property.isTrail.takeUntil hur).reverse,?_,?_,?_⟩
  · simpa only [SimpleGraph.Walk.edges_reverse,List.disjoint_reverse_left] using
      p₀.toPath.property.isTrail.disjoint_edges_takeUntil_dropUntil hup
  · simpa only [SimpleGraph.Walk.edges_reverse,List.disjoint_reverse_left,
      List.disjoint_reverse_right] using
      (walk_disjoint_mono hcp (fun _ h => h) (p.edges_takeUntil_subset_edges hup)).symm
  · simpa only [SimpleGraph.Walk.edges_reverse,List.disjoint_reverse_right] using
      (walk_disjoint_mono hcp (fun _ h => h) (p.edges_dropUntil_subset_edges hup)).symm

theorem walkQuartet_of_reachable {x y z t : V}
    (hxy : H.Reachable x y) (hxz : H.Reachable x z) (hxt : H.Reachable x t) :
    WalkQuartet H x y z t ∨ WalkQuartet H x z y t ∨ WalkQuartet H x t y z := by
  classical
  obtain ⟨u,p,q,r,hp,hq,hr,hpq,hpr,hqr⟩ := three_walks_from_reachable hxy hxz
  obtain ⟨s⟩ := hxt.symm.trans p.reachable.symm
  let S := p.support.toFinset ∪ q.support.toFinset ∪ r.support.toFinset
  have hu : u ∈ S := Finset.mem_union_left _
    (Finset.mem_union_left _ (List.mem_toFinset.mpr p.start_mem_support))
  obtain ⟨v,hv,hvs,hfirst⟩ := s.exists_mem_support_forall_mem_support_imp_eq S
    ⟨u,Finset.mem_filter.mpr ⟨hu,s.end_mem_support⟩⟩
  let a := s.takeUntil v hvs
  have hap : a.edges.Disjoint p.edges := by
    apply walk_edges_disjoint_of_single_support_intersection a p
    intro w hw hpw
    exact hfirst w (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr hpw))) hw
  have haq : a.edges.Disjoint q.edges := by
    apply walk_edges_disjoint_of_single_support_intersection a q
    intro w hw hqw
    exact hfirst w (Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr hqw))) hw
  have har : a.edges.Disjoint r.edges := by
    apply walk_edges_disjoint_of_single_support_intersection a r
    intro w hw hrw
    exact hfirst w (Finset.mem_union_right _ (List.mem_toFinset.mpr hrw)) hw
  rcases Finset.mem_union.mp hv with hv | hv
  · rcases Finset.mem_union.mp hv with hv | hv
    · exact Or.inr (Or.inr (quartet_of_split_arm p q r a hp
        (List.mem_toFinset.mp hv) hpq hpr hqr hap haq har))
    · have ht := quartet_of_split_arm q p r a hq
        (List.mem_toFinset.mp hv) hpq.symm hqr hpr haq hap har
      exact Or.inr (Or.inl ht.swap_pairs)
  · have ht := quartet_of_split_arm r p q a hr
      (List.mem_toFinset.mp hv) hpr.symm hqr.symm hpq har hap haq
    exact Or.inl ht.swap_pairs

end Percolation.BenjaminiSchramm

end OAI
