import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Encounter.Vertices

namespace OAI

/-! Tree branches, cluster retractions and terminal connecting trees. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open SimpleGraph
universe u
variable {V : Type u}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cutVertex_le_deleteEdge (T : SimpleGraph V) (x y : V) :
    cutVertex T x ≤ T.deleteEdges {s(x,y)} := by
  intro a b hab
  apply deleteEdges_adj.mpr
  refine ⟨hab.1,?_⟩
  intro he
  have hh : x ∈ s(a,b) := (Set.mem_singleton_iff.mp he) ▸ (by simp : x ∈ s(x,y))
  rcases Sym2.mem_iff.mp hh with hx | hx
  · exact hab.2.1 hx.symm
  · exact hab.2.2 hx.symm

theorem tree_cut_neighbors (T : SimpleGraph V) (ht : T.IsAcyclic) (x y z : V)
    (hy : T.Adj x y) (hz : T.Adj x z) (hyz : (cutVertex T x).Reachable y z) : y = z := by
  by_contra hn
  have hb := (isAcyclic_iff_forall_adj_isBridge.mp ht) hy
  have hd : (T.deleteEdges {s(x,y)}).Adj x z := by
    apply deleteEdges_adj.mpr
    refine ⟨hz,?_⟩
    intro he
    have hh := Sym2.eq_iff.mp (Set.mem_singleton_iff.mp he)
    rcases hh with ⟨_,hzy⟩ | ⟨hxy,hzx⟩
    · exact hn hzy.symm
    · exact hy.ne hxy
  exact (isBridge_iff.mp hb) (hd.reachable.trans (hyz.mono (cutVertex_le_deleteEdge T x y)).symm)

theorem cut_reachable_self_eq (T : SimpleGraph V) (x z : V)
    (h : (cutVertex T x).Reachable x z) : z = x := by
  induction h with
  | intro p =>
    cases p with
    | nil => rfl
    | cons hadj _ => exact False.elim (hadj.2.1 rfl)

theorem tree_branch_contains_leaf [Fintype V] (T : SimpleGraph V) (ht : T.IsTree)
    (x y : V) (hxy : T.Adj x y) :
    ∃ z, z ≠ x ∧ (cutVertex T x).Reachable y z ∧ T.degree z = 1 := by
  let C := ((cutVertex T x).connectedComponentMk y).supp
  have hyC : y ∈ C := (ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have hxC : x ∉ C := by
    intro h
    have hr : (cutVertex T x).Reachable y x := by
      exact (ConnectedComponent.eq.mp ((ConnectedComponent.mem_supp_iff _ _).mp h)).symm
    exact hxy.ne (cut_reachable_self_eq T x y hr.symm).symm
  have hr (z : V) (hz : z ∈ C) : (cutVertex T x).Reachable y z :=
    (ConnectedComponent.eq.mp ((ConnectedComponent.mem_supp_iff _ _).mp hz)).symm
  have hnbr (z : V) (hz : z ∈ C) (w : V) (hzw : T.Adj z w) : w = x ∨ w ∈ C := by
    by_cases hw : w = x
    · exact Or.inl hw
    · right
      apply (ConnectedComponent.mem_supp_iff _ _).mpr
      apply ConnectedComponent.sound
      exact (hr z hz).trans (Adj.reachable (G := cutVertex T x)
        ⟨hzw,fun h => hxC (h ▸ hz),hw⟩) |>.symm
  have hnx (z : V) (hz : z ∈ C) (hzx : T.Adj z x) : z = y :=
    (tree_cut_neighbors T ht.isAcyclic x y z hxy hzx.symm (hr z hz)).symm
  have hccon : (T.induce C).Connected := by
    apply SimpleGraph.Connected.mono (G := (cutVertex T x).induce C)
    · intro a b hab; exact hab.1
    · exact ((cutVertex T x).connectedComponentMk y).connected_toSimpleGraph
  have hc : (T.induce C).IsTree := ⟨hccon,ht.isAcyclic.induce C⟩
  by_cases he : ∃ z ∈ C, z ≠ y
  · obtain ⟨z,hz,hzy⟩ := he
    let : Nontrivial C := ⟨⟨⟨z,hz⟩,⟨y,hyC⟩,fun h => hzy (congrArg Subtype.val h)⟩⟩
    obtain ⟨a,b,hab,ha,hb⟩ := hc.exists_ne_and_degree_eq_one
    have hex : ∃ a : C, a.val ≠ y ∧ (T.induce C).degree a = 1 := by
      by_cases hay : a.val = y
      · refine ⟨b,?_,hb⟩
        intro hby
        exact hab (Subtype.ext (hay.trans hby.symm))
      · exact ⟨a,hay,ha⟩
    obtain ⟨a,hay,ha⟩ := hex
    refine ⟨a.val,fun h => hxC (h ▸ a.property),hr _ a.property,?_⟩
    have hn : T.neighborSet a.val ⊆ C := by
      intro w hw
      rcases hnbr a.val a.property w hw with rfl | hwc
      · exact False.elim (hay (hnx a.val a.property hw))
      · exact hwc
    rwa [T.degree_induce_of_neighborSet_subset hn] at ha
  · push Not at he
    refine ⟨y,hxy.ne.symm,Reachable.refl y,?_⟩
    apply degree_eq_one_iff_existsUnique_adj.mpr
    refine ⟨x,hxy.symm,?_⟩
    intro w hw
    rcases hnbr y hyC w hw with hwx | hwC
    · exact hwx
    · exact False.elim (hw.ne (he w hwC).symm)

theorem pruned_tree_branch_marked [Fintype V] (T : SimpleGraph V) (ht : T.IsTree)
    (S : Finset V) (hpr : ∀ z, z ∉ S → 2 ≤ T.degree z)
    (x y : V) (hxy : T.Adj x y) :
    ∃ z ∈ S, z ≠ x ∧ (cutVertex T x).Reachable y z := by
  obtain ⟨z,hzx,hz,hd⟩ := tree_branch_contains_leaf T ht x y hxy
  refine ⟨z,?_,hzx,hz⟩
  by_contra hn
  have hh := hpr z hn
  omega

theorem tree_three_leaves_branch [Fintype V] (T : SimpleGraph V) (ht : T.IsTree)
    (S : Finset V) (hcard : 3 ≤ S.card) (hleaf : ∀ z ∈ S, T.degree z = 1) :
    ∃ x, 3 ≤ T.degree x := by
  by_contra hn
  have hd (x : V) : T.degree x ≤ 2 := by have := not_exists.mp hn x; omega
  have hs : (∑ x : V, (T.degree x + (if x ∈ S then 1 else 0))) ≤
      ∑ x : V, (2:ℕ) := by
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : x ∈ S
    · simp only [hx,ite_true,hleaf x hx]; omega
    · simpa only [hx,ite_false,add_zero] using hd x
  have hsum : (∑ x : V, if x ∈ S then (1:ℕ) else 0) = S.card := by
    simp
  rw [Finset.sum_add_distrib,hsum,T.sum_degrees_eq_twice_card_edges] at hs
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  have he := ht.card_edgeFinset
  have hc : S.card ≤ Fintype.card V := Finset.card_le_univ S
  omega

theorem pruned_tree_three_branches [Fintype V] (T : SimpleGraph V) (ht : T.IsTree)
    (S : Finset V) (hcard : 3 ≤ S.card) (hleaf : ∀ z ∈ S, T.degree z = 1)
    (hpr : ∀ z, z ∉ S → 2 ≤ T.degree z) :
    ∃ x a b c, x ∉ S ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
      a ≠ x ∧ b ≠ x ∧ c ≠ x ∧
      ¬ (cutVertex T x).Reachable a b ∧
      ¬ (cutVertex T x).Reachable a c ∧
      ¬ (cutVertex T x).Reachable b c := by
  obtain ⟨x,hx⟩ := tree_three_leaves_branch T ht S hcard hleaf
  have hxS : x ∉ S := by intro h; have := hleaf x h; omega
  have hnc : 2 < (T.neighborFinset x).card := by simpa using (show 2 < T.degree x by omega)
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ := Finset.two_lt_card_iff.mp hnc
  have hau := (T.mem_neighborFinset x u).mp hu
  have hav := (T.mem_neighborFinset x v).mp hv
  have haw := (T.mem_neighborFinset x w).mp hw
  obtain ⟨a,ha,hax,hua⟩ := pruned_tree_branch_marked T ht S hpr x u hau
  obtain ⟨b,hb,hbx,hvb⟩ := pruned_tree_branch_marked T ht S hpr x v hav
  obtain ⟨c,hc,hcx,hwc⟩ := pruned_tree_branch_marked T ht S hpr x w haw
  refine ⟨x,a,b,c,hxS,ha,hb,hc,hax,hbx,hcx,?_,?_,?_⟩
  · intro h; exact huv (tree_cut_neighbors T ht.isAcyclic x u v hau hav
      (hua.trans (h.trans hvb.symm)))
  · intro h; exact huw (tree_cut_neighbors T ht.isAcyclic x u w hau haw
      (hua.trans (h.trans hwc.symm)))
  · intro h; exact hvw (tree_cut_neighbors T ht.isAcyclic x v w hav haw
      (hvb.trans (h.trans hwc.symm)))
end Percolation

namespace Percolation
open SimpleGraph
universe u v w
variable {V : Type u} {E : Type v} {W : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_cluster_retraction (G : BondGraph V E) (η : Set E) (f : W ↪ V)
    (hsep : ∀ a b, Conn G η (f a) (f b) → a = b) (x : W) :
    ∃ r : V → W, (∀ a, r (f a) = a) ∧
      ∀ a b, Conn G η a b → r a = r b := by
  let r : V → W := fun y => if h : ∃ z, Conn G η (f z) y then h.choose else x
  have hval (y : V) (z : W) (hz : Conn G η (f z) y) : r y = z := by
    have hex : ∃ z, Conn G η (f z) y := ⟨z,hz⟩
    dsimp [r]
    rw [dite_eq_left hex]
    exact hsep _ _ (conn_trans G η hex.choose_spec (conn_symm G η hz))
  refine ⟨r,fun a => hval _ _ (conn_refl G η _),?_⟩
  intro a b hab
  by_cases ha : ∃ z, Conn G η (f z) a
  · obtain ⟨z,hz⟩ := ha
    rw [hval a z hz,hval b z (conn_trans G η hz hab)]
  · have hb : ¬ ∃ z, Conn G η (f z) b := by
      rintro ⟨z,hz⟩
      exact ha ⟨z,conn_trans G η hz (conn_symm G η hab)⟩
    simp only [r,dite_eq_right ha,dite_eq_right hb]

theorem glued_cut_conn (G : BondGraph V E) (η P : Set E) (T : SimpleGraph W)
    (f : W ↪ V) (r : V → W) (hr : ∀ a, r (f a) = a)
    (hη : ∀ a b, Conn G η a b → r a = r b)
    (hP : ∀ e ∈ P, ∃ a b, T.Adj a b ∧ G e = s(f a,f b))
    (x : W) {a b : V} (hab : Conn G (cutConfig G (η ∪ P) (f x)) a b) :
    (cutVertex T x).Reachable (r a) (r b) := by
  induction hab with
  | refl => exact .refl _
  | @tail a b hab hed ih =>
    obtain ⟨e,⟨he,hx⟩,hGe⟩ := hed
    rcases he with he | he
    · have hh := hη a b ((conn_refl G η a).tail ⟨e,he,hGe⟩)
      rwa [←hh]
    · obtain ⟨u,v,huv,heq⟩ := hP e he
      have hne : u ≠ x ∧ v ≠ x := by
        rw [heq] at hx
        simpa [Sym2.mem_iff,f.injective.eq_iff,eq_comm] using hx
      have hkv : (cutVertex T x).Adj u v := ⟨huv,hne⟩
      have habuv := Sym2.eq_iff.mp (hGe.symm.trans heq)
      rcases habuv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rw [hr] at ih ⊢
        exact ih.trans hkv.reachable
      · rw [hr] at ih ⊢
        exact ih.trans hkv.symm.reachable

theorem glued_conn (G : BondGraph V E) (ω : Set E) (T : SimpleGraph W)
    (f : W → V) (hT : T.Connected)
    (he : ∀ a b, T.Adj a b → ∃ e ∈ ω, G e = s(f a,f b)) (a b : W) :
    Conn G ω (f a) (f b) := by
  obtain ⟨p⟩ := hT a b
  induction p with
  | nil => exact conn_refl G ω _
  | @cons a b c hab p ih =>
    exact conn_trans G ω ((conn_refl G ω _).tail (he a b hab)) ih

end Percolation

namespace Percolation
open SimpleGraph
universe u
variable {V : Type u}
attribute [local instance] Classical.propDecidable Classical.decEq

def terminalGraph (H : SimpleGraph V) (A : Finset V) (v w : Fin 3 → V) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ ((a ∈ A ∧ b ∈ A) ∨
    ∃ i, (a = v i ∧ b = w i) ∨ (a = w i ∧ b = v i))
  symm := ⟨by
    intro a b h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with h | ⟨i,h|h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨i,Or.inr h.symm⟩
    · exact Or.inr ⟨i,Or.inl h.symm⟩⟩
  loopless := ⟨fun a h => H.loopless.irrefl a h.1⟩

theorem terminalGraph_touch (H : SimpleGraph V) (A : Finset V) (v w : Fin 3 → V)
    (hv : ∀ i, v i ∈ A) {a b : V} (h : (terminalGraph H A v w).Adj a b) :
    a ∈ A ∨ b ∈ A := by
  rcases h.2 with h | ⟨i,h|h⟩
  · exact Or.inl h.1
  · exact Or.inl (h.1 ▸ hv i)
  · exact Or.inr (h.2 ▸ hv i)

theorem terminalGraph_leaf (H : SimpleGraph V) (A : Finset V) (v w : Fin 3 → V)
    (hv : ∀ i, v i ∈ A) (hw : ∀ i, w i ∉ A) (hwi : Function.Injective w)
    (i : Fin 3) {y : V} (h : (terminalGraph H A v w).Adj (w i) y) : y = v i := by
  rcases h.2 with h | ⟨j,h|h⟩
  · exact False.elim (hw i h.1)
  · exact False.elim (hw i (h.1 ▸ hv j))
  · have hij := hwi h.1
    simpa only [hij] using h.2

theorem terminalGraph_connected (H : SimpleGraph V) (A : Finset V) (v w : Fin 3 → V)
    (hv : ∀ i, v i ∈ A) (hadj : ∀ i, H.Adj (v i) (w i))
    (hA : (H.induce (A:Set V)).Connected) :
    ((terminalGraph H A v w).induce ((A ∪ Finset.univ.image w : Finset V):Set V)).Connected := by
  let D := A ∪ Finset.univ.image w
  let K := terminalGraph H A v w
  have hAD : A ⊆ D := Finset.subset_union_left
  let f : (H.induce (A:Set V)) →g (K.induce (D:Set V)) :=
    ⟨fun a => ⟨a.val,hAD a.property⟩,fun {a b} hab => ⟨hab,Or.inl ⟨a.property,b.property⟩⟩⟩
  let z : (D:Set V) := ⟨v 0,hAD (hv 0)⟩
  have connA (a : V) (ha : a ∈ A) : (K.induce (D:Set V)).Reachable ⟨a,hAD ha⟩ z :=
    (hA ⟨a,ha⟩ ⟨v 0,hv 0⟩).map f
  have connD (a : (D:Set V)) : (K.induce (D:Set V)).Reachable a z := by
    rcases Finset.mem_union.mp a.property with ha | ha
    · exact connA a.val ha
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
      have hK : (K.induce (D:Set V)).Adj a ⟨v i,hAD (hv i)⟩ := by
        change K.Adj a.val (v i)
        rw [←hi]
        exact ⟨(hadj i).symm,Or.inr ⟨i,Or.inr ⟨rfl,rfl⟩⟩⟩
      exact hK.reachable.trans (connA _ (hv i))
  let : Nonempty (D:Set V) := ⟨z⟩
  exact ⟨fun a b => (connD a).trans (connD b).symm⟩

theorem exists_terminal_tree (H : SimpleGraph V) (A : Finset V) (v w : Fin 3 → V)
    (hv : ∀ i, v i ∈ A) (hw : ∀ i, w i ∉ A) (hwi : Function.Injective w)
    (hadj : ∀ i, H.Adj (v i) (w i))
    (hA : (H.induce (A:Set V)).Connected) :
    ∃ D : Finset V, D ⊆ A ∪ Finset.univ.image w ∧ Finset.univ.image w ⊆ D ∧
      ∃ T : SimpleGraph (D:Set V), T ≤ (terminalGraph H A v w).induce (D:Set V) ∧
        T.IsTree ∧ ∃ x a b c : (D:Set V), x.val ∈ A ∧
          a.val ∈ Finset.univ.image w ∧ b.val ∈ Finset.univ.image w ∧
          c.val ∈ Finset.univ.image w ∧
          ¬ (cutVertex T x).Reachable a b ∧
          ¬ (cutVertex T x).Reachable a c ∧
          ¬ (cutVertex T x).Reachable b c := by
  let S := Finset.univ.image w
  have hS : S.Nonempty := ⟨w 0,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  obtain ⟨D,hD,hSD,T,hTK,hT,hpr⟩ := exists_pruned_connector
    (terminalGraph H A v w) S (A ∪ S) hS Finset.subset_union_right
    (terminalGraph_connected H A v w hv hadj hA)
  let s : Fin 3 → (D:Set V) := fun i => ⟨w i,hSD (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩
  have hsi : Function.Injective s := fun _ _ h => hwi (congrArg Subtype.val h)
  let S' := Finset.univ.image s
  have hS' (z : (D:Set V)) : z ∈ S' ↔ z.val ∈ S := by
    simp only [S',S,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨i,rfl⟩
    · rintro ⟨i,hi⟩; exact ⟨i,Subtype.ext hi⟩
  have hcard : S'.card = 3 := by
    rw [Finset.card_image_of_injective _ hsi]
    simp
  let : Nontrivial (D:Set V) := ⟨⟨s 0,s 1,fun h => by have := hsi h; norm_num at this⟩⟩
  have hleaf (z : (D:Set V)) (hz : z ∈ S') : T.degree z = 1 := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ((hS' z).mp hz)
    have hpos : 0 < T.degree z := lt_of_lt_of_le
      hT.connected.preconnected.minDegree_pos_of_nontrivial (T.minDegree_le_degree z)
    obtain ⟨a,ha⟩ := (T.degree_pos_iff_exists_adj z).mp hpos
    apply degree_eq_one_iff_existsUnique_adj.mpr
    refine ⟨a,ha,?_⟩
    intro b hb
    apply Subtype.ext
    have ha' : a.val = v i := terminalGraph_leaf H A v w hv hw hwi i (by rw [hi]; exact hTK ha)
    have hb' : b.val = v i := terminalGraph_leaf H A v w hv hw hwi i (by rw [hi]; exact hTK hb)
    exact hb'.trans ha'.symm
  obtain ⟨x,a,b,c,hx,ha,hb,hc,_,_,_,hab,hac,hbc⟩ :=
    pruned_tree_three_branches T hT S' (by omega) hleaf
      (fun z hz => hpr z (fun h => hz ((hS' z).mpr h)))
  have hxA : x.val ∈ A := by
    rcases Finset.mem_union.mp (hD x.property) with h | h
    · exact h
    · exact False.elim (hx ((hS' x).mpr h))
  exact ⟨D,hD,hSD,T,hTK,hT,x,a,b,c,hxA,(hS' a).mp ha,(hS' b).mp hb,
    (hS' c).mp hc,hab,hac,hbc⟩
end Percolation

end OAI
