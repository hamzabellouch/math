import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.ColouredPaths
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.LongPaths

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem alpha_two_adj {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hα : G.indepNum ≤ 2) {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hx : ¬ G.Adj x z) (hy : ¬ G.Adj y z) : G.Adj x y := by
  classical
  by_contra hxyadj
  have hI : G.IsIndepSet {x, y, z} := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact hxyadj
    · exact hx
    · exact fun h => hxyadj h.symm
    · exact (hab rfl).elim
    · exact hy
    · exact fun h => hx h.symm
    · exact fun h => hy h.symm
    · exact (hab rfl).elim
  have hc := (indep_ncard_le hI).trans hα
  simp [Set.ncard_insert_of_notMem, hxy, hxz, hyz] at hc

theorem clique_ncard_le_cliqueNum {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S : Set V} (hS : G.IsClique S) : S.ncard ≤ G.cliqueNum := by
  classical
  have hh : G.IsClique (S.toFinset : Set V) := by simpa using hS
  simpa only [Set.ncard_eq_toFinset_card'] using hh.card_le_cliqueNum

 
theorem clique_of_anticomplete_vertex {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hα : G.indepNum ≤ 2) {S : Set V} {z : V} (hz : z ∉ S)
    (hanti : ∀ x ∈ S, ¬ G.Adj x z) : G.IsClique S := by
  intro x hx y hy hxy
  exact alpha_two_adj hα (z := z) hxy (fun he => hz (he ▸ hx))
    (fun he => hz (he ▸ hy)) (hanti x hx) (hanti y hy)

 
theorem connected_of_alpha_two_large {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (hα : G.indepNum ≤ 2) (ht : G.cliqueNum ≤ t)
    (hcard : 2 * t < Fintype.card V) : G.Connected := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let := hne
  refine ⟨?_⟩
  intro x y
  by_contra hxy
  let S := {v | G.Reachable x v}
  have hx : x ∈ S := SimpleGraph.Reachable.rfl
  have hy : y ∉ S := hxy
  have hanti : ∀ a ∈ S, ∀ b ∈ Sᶜ, ¬ G.Adj a b := by
    intro a ha b hb hab
    exact hb (ha.trans hab.reachable)
  have hS : G.IsClique S := clique_of_anticomplete_vertex hα hy (fun a ha => hanti a ha y hy)
  have hR : G.IsClique Sᶜ := clique_of_anticomplete_vertex hα
    (show x ∉ Sᶜ from fun hh => hh hx) (fun b hb hab => hanti x hx b hb hab.symm)
  have hcS := (clique_ncard_le_cliqueNum hS).trans ht
  have hcR := (clique_ncard_le_cliqueNum hR).trans ht
  have hsum := Set.ncard_add_ncard_compl S
  rw [Nat.card_eq_fintype_card] at hsum
  omega

 

theorem deletion_connected_of_alpha_two_large {V : Type*} [Fintype V]
    {G : SimpleGraph V} {t : ℕ} (hα : G.indepNum ≤ 2) (ht : G.cliqueNum ≤ t)
    (hcard : 2 * t < Fintype.card V) (v x y : V) (hxv : x ≠ v) (hyv : y ≠ v) :
    (within G {w | w ≠ v}).Reachable x y := by
  classical
  let D := within G {w | w ≠ v}
  by_contra hxy
  let A : Set V := {w | D.Reachable x w}
  let B : Set V := {w | w ≠ v} \ A
  have hxA : x ∈ A := SimpleGraph.Reachable.rfl
  have hAv : ∀ a ∈ A, a ≠ v := by
    rintro a ⟨p⟩
    exact within_support p hxv a p.end_mem_support
  have hyB : y ∈ B := ⟨hyv, hxy⟩
  have hanti : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
    intro a ha b hb hab
    exact hb.2 (ha.trans (show D.Adj a b from ⟨hab, hAv a ha, hb.1⟩).reachable)
  have hA : G.IsClique A := clique_of_anticomplete_vertex hα hyB.2
    (fun a ha => hanti a ha y hyB)
  have hB : G.IsClique B := clique_of_anticomplete_vertex hα
    (show x ∉ B from fun hh => hh.2 hxA) (fun b hb hab => hanti x hxA b hb hab.symm)
  have hcA := (clique_ncard_le_cliqueNum hA).trans ht
  have hcB := (clique_ncard_le_cliqueNum hB).trans ht
  have hvAB : v ∉ A ∪ B := by
    rintro (ha | hb)
    · exact hAv v ha rfl
    · exact hb.1 rfl
  have huniv : insert v (A ∪ B) = Set.univ := by
    ext w
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_univ, iff_true]
    by_cases hwv : w = v
    · exact Or.inl hwv
    · by_cases hw : w ∈ A
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr ⟨hwv, hw⟩)
  have hdis : Disjoint A B := Set.disjoint_left.mpr (fun a ha hb => hb.2 ha)
  have hsum : A.ncard + B.ncard + 1 = Fintype.card V := by
    have hh := congrArg Set.ncard huniv
    simpa only [Set.ncard_insert_of_notMem hvAB, Set.ncard_union_eq hdis,
      Set.ncard_univ, Nat.card_eq_fintype_card] using hh
  have hAc : A.ncard = t := by omega
  have hBc : B.ncard = t := by omega
  have hone : (∀ a ∈ A, G.Adj v a) ∨ (∀ b ∈ B, G.Adj v b) := by
    by_cases ha : ∀ a ∈ A, G.Adj v a
    · exact Or.inl ha
    · push Not at ha
      obtain ⟨a, ha, hva⟩ := ha
      refine Or.inr (fun b hb => ?_)
      exact alpha_two_adj hα (Ne.symm hb.1) (Ne.symm (hAv a ha))
        (fun he => hb.2 (he ▸ ha)) hva (fun h => hanti a ha b hb h.symm)
  rcases hone with ha | hb
  · have hcl : G.IsClique (insert v A) := hA.insert (fun a ha' _ => ha a ha')
    have hc := (clique_ncard_le_cliqueNum hcl).trans ht
    rw [Set.ncard_insert_of_notMem (fun hv => hAv v hv rfl), hAc] at hc
    omega
  · have hcl : G.IsClique (insert v B) := hB.insert (fun b hb' _ => hb b hb')
    have hc := (clique_ncard_le_cliqueNum hcl).trans ht
    rw [Set.ncard_insert_of_notMem (fun hv => hv.1 rfl), hBc] at hc
    omega

 

theorem degree_two_of_deletion_connected {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (hdel : ∀ v x y, x ≠ v → y ≠ v → (within G {w | w ≠ v}).Reachable x y)
    (x : V) : 2 ≤ G.degree x := by
  classical
  obtain ⟨y, _, hyx⟩ := exists_mem_ne_of_ncard (E := Set.univ) (w₀ := x)
    (by simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using (by omega : 2 ≤ Fintype.card V))
  obtain ⟨p⟩ := hconn.preconnected x y
  have hplen : 0 < p.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
    (fun hn => hyx hn.eq.symm)
  let w := p.getVert 1
  have hxw : G.Adj x w := by
    simpa only [SimpleGraph.Walk.getVert_zero, zero_add]
      using (p.adj_getVert_succ (i := 0) hplen)
  have hex : ∃ z : V, z ≠ x ∧ z ≠ w := by
    by_contra hn
    push Not at hn
    have hsub : (Set.univ : Set V) ⊆ {x, w} := by
      intro z _
      by_cases hz : z = x
      · exact Or.inl hz
      · exact Or.inr (hn z hz)
    have hh := Set.ncard_le_ncard hsub
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Set.ncard_pair hxw.ne] at hh
    omega
  obtain ⟨z, hzx, hzw⟩ := hex
  obtain ⟨q⟩ := hdel w x z hxw.ne hzw
  have hqlen : 0 < q.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
    (fun hn => hzx hn.eq.symm)
  let u := q.getVert 1
  have hxu : (within G {a | a ≠ w}).Adj x u := by
    simpa only [SimpleGraph.Walk.getVert_zero, zero_add]
      using q.adj_getVert_succ (i := 0) hqlen
  have hh : 1 < (G.neighborSet x).ncard := (Set.one_lt_ncard).mpr
    ⟨w, hxw, u, hxu.1, Ne.symm hxu.2.2⟩
  rw [ncard_neighborSet] at hh
  omega

 

theorem hamiltonian_of_alpha_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V) (hα : G.indepNum ≤ 2)
    (hdel : ∀ v x y, x ≠ v → y ≠ v → (within G {w | w ≠ v}).Reachable x y) :
    ∃ x, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = Fintype.card V := by
  classical
  let : Nonempty V := hconn.nonempty
  have hdegree := degree_two_of_deletion_connected hconn hcard hdel
  obtain ⟨x, y, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  obtain ⟨a, b, P, hP, hPlen⟩ := long_path_min_degree (by omega : 2 ≤ 2) hconn hdegree
  have hlen : 2 ≤ p.length := by
    have hh := hmax a b P hP
    omega
  have hW : 1 < p.support.length := by rw [SimpleGraph.Walk.length_support]; omega
  have hyN : ∀ z, G.Adj y z → z ∈ p.support :=
    longest_path_endpoint_neighbors p hp (fun z q hq => hmax x z q hq)
  have hxN : ∀ z, G.Adj x z → z ∈ p.support := by
    intro z hxz
    have hh := longest_path_endpoint_neighbors p.reverse hp.reverse
      (fun z q hq => by simpa using hmax y z q hq) z hxz
    simpa using hh
  have hspan : ∀ z, z ∈ p.support := by
    intro z
    by_contra hz
    have hxy : x ≠ y := by
      intro hh
      have hn := (hp.nil_iff_eq).mpr hh
      have hh := hn.length_eq_zero
      omega
    have hxyadj := alpha_two_adj hα (z := z) hxy
      (fun hh => hz (by rw [← hh]; exact p.start_mem_support))
      (fun hh => hz (by rw [← hh]; exact p.end_mem_support))
      (fun hh => hz (hxN z hh)) (fun hh => hz (hyN z hh))
    let c := SimpleGraph.Walk.cons hxyadj.symm p
    have hc : c.IsCycle := path_close_cycle p hp hlen hxyadj.symm
    have hzc : z ∉ c.support := by
      simp only [c, SimpleGraph.Walk.support_cons, List.mem_cons]
      exact fun hh => hh.elim (fun hh => hz (by rw [hh]; exact p.end_mem_support)) hz
    obtain ⟨u, v, q, hq, hqlen⟩ := extend_nonspanning_cycle hconn c hc ⟨z, hzc⟩
    have hh := hmax u v q hq
    simp only [c, SimpleGraph.Walk.length_cons] at hqlen
    omega
  have hcardp : p.length + 1 = Fintype.card V := by
    have hh : p.support.toFinset = Finset.univ := by ext z; simp [hspan]
    have hc := congrArg Finset.card hh
    simpa only [List.toFinset_card_of_nodup hp.support_nodup,
      SimpleGraph.Walk.length_support, Finset.card_univ] using hc
  let E := pathEnds G x p.support
  have hxE : x ∉ E := pathEnds_no_start hW
  have hyE : y ∈ E := ⟨p, hp, .refl _⟩
  have hEc : 2 ≤ E.ncard :=
    (hdegree y).trans (degree_le_card_pathEnds p hp (.refl _) hyN)
  have hclose : ∃ e ∈ E, G.Adj x e := by
    by_contra hn
    push Not at hn
    have hcl : G.IsClique E := clique_of_anticomplete_vertex hα hxE
      (fun e he he' => hn e he he'.symm)
    obtain ⟨j, hjpos, hjlen, hseg⟩ := pathEnds_final_segment p hp (.refl _) hcl hW
    have hjtwo : 2 ≤ j := by
      by_contra hh
      have hjone : j = 1 := by omega
      have hfirst := p.adj_getVert_succ (i := 0) (by omega)
      simp only [SimpleGraph.Walk.getVert_zero, zero_add] at hfirst
      exact hn (p.getVert 1) ((hseg 1 (by omega)).mpr (by omega)) hfirst
    let u := p.getVert (j - 1)
    let w₀ := p.getVert j
    have huE : u ∉ E := by
      exact fun hu => by have hh := (hseg (j - 1) (by omega)).mp hu; omega
    have hxw : x ≠ w₀ := by
      intro hh
      exact hxE (hh ▸ (hseg j hjlen).mpr le_rfl)
    have hux : u ≠ x := by
      intro hh
      have hh' := (hp.getVert_eq_start_iff (show j - 1 ≤ p.length by omega)).mp hh
      omega
    obtain ⟨w₁, hw₁, hw₁ne⟩ := exists_mem_ne_of_ncard (w₀ := w₀) hEc
    obtain ⟨q⟩ := hdel w₀ x w₁ hxw hw₁ne
    obtain ⟨d, hd, hdout, hdin⟩ := q.exists_boundary_dart Eᶜ hxE
      (show w₁ ∉ Eᶜ from fun hh => hh hw₁)
    have hdinE : d.snd ∈ E := not_not.mp hdin
    have hdinne : d.snd ≠ w₀ := d.adj.2.2
    have hpartial := pathEnds_partial_attachment p hp (fun v q hq => hmax x v q hq)
      hcl hjpos hjlen hseg hdinE hdinne d.fst d.adj.1.symm
    have hdu : d.fst = u := hpartial.resolve_left hdout
    have hentry : G.Adj u d.snd := hdu ▸ d.adj.1
    have hattach := pathEnds_attachment_of_two_entries p hp (fun v q hq => hmax x v q hq)
      hcl hjpos hjlen hseg hdinE hdinne hentry
    have hyu : y ≠ u := fun hh => huE (hh ▸ hyE)
    obtain ⟨q'⟩ := hdel u x y hux.symm hyu
    obtain ⟨d', _, hd'out, hd'in⟩ := q'.exists_boundary_dart Eᶜ hxE
      (show y ∉ Eᶜ from fun hh => hh hyE)
    have hlast := hattach d'.snd (not_not.mp hd'in) d'.fst d'.adj.1.symm
    exact d'.adj.2.1 (hlast.resolve_left hd'out)
  obtain ⟨e, he, hxe⟩ := hclose
  obtain ⟨q, hq, hperm⟩ := he
  have hqlen : q.length = p.length := by
    have hh := hperm.length_eq
    simp only [SimpleGraph.Walk.length_support] at hh
    omega
  refine ⟨e, .cons hxe.symm q, path_close_cycle q hq (by omega) hxe.symm, ?_⟩
  simpa only [SimpleGraph.Walk.length_cons, hqlen] using hcardp

end CycleClique

end OAI
