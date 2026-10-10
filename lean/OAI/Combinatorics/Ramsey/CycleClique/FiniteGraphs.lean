import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.ChainProfiles
import OAI.Combinatorics.Ramsey.CycleClique.ChainRearrangement
import OAI.Combinatorics.Ramsey.CycleClique.CycleShortening
import OAI.Combinatorics.Ramsey.CycleClique.Exceptional
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorBalls
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorPaths
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.IndependenceTwo
import OAI.Combinatorics.Ramsey.CycleClique.InducedGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LargeSystems
import OAI.Combinatorics.Ramsey.CycleClique.MarkedChains
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

noncomputable def chosenChain {V : Type*} (Q : Set V) (c : List V) : List V :=
  if c.length = 4 then c.tail.dropLast else (markedReps Q true c).filter (fun x => x ∉ Q)

 theorem chosenChain_sublist {V : Type*} (Q : Set V) (c : List V) :
    (chosenChain Q c).Sublist c := by
  classical
  unfold chosenChain
  split_ifs
  · exact (List.dropLast_sublist _).trans (List.tail_sublist _)
  · exact List.filter_sublist.trans (markedReps_sublist Q true c)

 theorem ClosedChain.four {V : Type*} {G : SimpleGraph V} {Q : Set V} {c : List V}
    (h : ClosedChain G Q c) (hl : c.length = 4) :
    ∃ u a b v, c = [u,a,b,v] ∧ u ∈ Q ∧ v ∈ Q ∧ a ∉ Q ∧ b ∉ Q := by
  rcases c with _ | ⟨u,c⟩ <;> try simp at hl
  rcases c with _ | ⟨a,c⟩ <;> try simp at hl
  rcases c with _ | ⟨b,c⟩ <;> try simp at hl
  rcases c with _ | ⟨v,c⟩ <;> try simp at hl
  have hc : c = [] := List.length_eq_zero_iff.mp (by simpa using hl)
  subst c
  have hu : u ∈ Q := h.ends.1 u (by simp)
  have hv : v ∈ Q := h.ends.2 v (by simp)
  have ha : a ∉ Q := h.positive.rel.resolve_left (not_not.mpr hu)
  have hb : b ∉ Q := h.positive.tail.tail.rel.resolve_right (not_not.mpr hv)
  exact ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩

 theorem ClosedChain.chosen_rep {V : Type*} {G : SimpleGraph V} {Q : Set V} {c : List V}
    (h : ClosedChain G Q c) {x : V} (hx : x ∈ chosenChain Q c) :
    x ∉ Q ∧ ∃ b : Bool, x ∈ markedReps Q true (flipChain b c) := by
  classical
  by_cases hl : c.length = 4
  · obtain ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩ := h.four hl
    have hh : x = a ∨ x = b := by simpa [chosenChain] using hx
    rcases hh with rfl | rfl
    · exact ⟨ha, false, by simp [flipChain, markedReps, hu]⟩
    · exact ⟨hb, true, by simp [flipChain, markedReps, hv]⟩
  · have hx' := List.mem_filter.mp (show x ∈ (markedReps Q true c).filter (fun x => x ∉ Q) by
      simpa only [chosenChain, ite_eq_right hl] using hx)
    exact ⟨of_decide_eq_true hx'.2, false, by simpa [flipChain] using hx'.1⟩

 theorem ClosedChain.interior_count {V : Type*} {G : SimpleGraph V} {Q : Set V} {c : List V}
    (h : ClosedChain G Q c) (hn : c.Nodup) {A : List ℕ} (hA : ChainAmounts Q c A) :
    ((markedReps Q true c).filter (fun x => x ∉ Q)).length = A.length := by
  classical
  have hl := markedReps_length Q true c h.nonempty h.ends.2
  have hh := (markedReps Q true c).length_eq_countP_add_countP (fun x => decide (x ∈ Q))
  rw [h.reps_Q_count hn] at hh
  simp only [Bool.not_eq_true, decide_eq_false_iff_not, List.countP_eq_length_filter] at hh
  have hc := hA.count.1
  simp only [ite_true] at hl
  omega

 theorem ClosedChain.chosen_count {V : Type*} {G : SimpleGraph V} {Q : Set V} {c : List V}
    (h : ClosedChain G Q c) (hn : c.Nodup) {A : List ℕ} (hA : ChainAmounts Q c A)
    (ha : ∀ a ∈ A, 2 ≤ a) (hc1 : c.length ≠ 1) :
    2 * c.countP (fun x => decide (x ∈ Q)) ≤ (chosenChain Q c).length + A.sum := by
  classical
  obtain ⟨hc, hl, _⟩ := hA.count
  have hs := list_sum_lower A 2 ha
  have hAp : 1 ≤ A.length := by
    by_contra! hh
    have he : A = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [he, List.length_nil, List.sum_nil] at hl
    exact hc1 (by omega)
  by_cases h4 : c.length = 4
  · obtain ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩ := h.four h4
    simp only [chosenChain, List.length_cons, List.length_nil, Nat.reduceAdd, ite_true,
      List.tail_cons, List.dropLast_cons_cons, List.dropLast_singleton]
    simp only [List.length_cons, List.length_nil] at hl
    omega
  · have hi := h.interior_count hn hA
    simp only [chosenChain, ite_eq_right h4, hi]
    by_cases hA1 : A.length = 1
    · have hs3 : 3 ≤ A.sum := by omega
      omega
    · omega

 theorem PathSystem.orient_rep_chain {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (f : List V → Bool) {c : List V} (hc : c ∈ P.chains)
    {x : V} (hx : x ∈ markedReps Q true (flipChain (f c) c)) : x ∈ (P.orient f).reps := by
  apply (P.orient f).rep_of_chain (show flipChain (f c) c ∈ (P.orient f).chains from ?_) hx
  rw [PathSystem.orient_chains]
  exact List.mem_map.mpr ⟨c,hc,rfl⟩

 theorem PathSystem.chosen_rep {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c : List V} (hc : c ∈ P.chains) {x : V}
    (hx : x ∈ chosenChain Q c) : x ∉ Q ∧ ∃ f : List V → Bool, x ∈ (P.orient f).reps := by
  obtain ⟨hxQ,b,hb⟩ := (P.closed_chain hc).chosen_rep hx
  exact ⟨hxQ, fun _ => b, P.orient_rep_chain _ hc hb⟩

 theorem PathSystem.chosen_pair {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c c' : List V} (hc : c ∈ P.chains) (hc' : c' ∈ P.chains)
    {x y : V} (hx : x ∈ chosenChain Q c) (hy : y ∈ chosenChain Q c') (hxy : x ≠ y) :
    (∃ f : List V → Bool, x ∈ (P.orient f).reps ∧ y ∈ (P.orient f).reps) ∨
    (∃ u v, c = [u,x,y,v]) ∨ (∃ u v, c = [u,y,x,v]) := by
  classical
  by_cases hcc : c = c'
  · subst c'
    by_cases h4 : c.length = 4
    · obtain ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩ := (P.closed_chain hc).four h4
      have hx' : x = a ∨ x = b := by simpa [chosenChain] using hx
      have hy' : y = a ∨ y = b := by simpa [chosenChain] using hy
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
      · exact (hxy rfl).elim
      · exact Or.inr (Or.inl ⟨u,v,rfl⟩)
      · exact Or.inr (Or.inr ⟨u,v,rfl⟩)
      · exact (hxy rfl).elim
    · have hx' : x ∈ markedReps Q true c := List.mem_of_mem_filter (by
        simpa only [chosenChain, ite_eq_right h4] using hx)
      have hy' : y ∈ markedReps Q true c := List.mem_of_mem_filter (by
        simpa only [chosenChain, ite_eq_right h4] using hy)
      exact Or.inl ⟨fun _ => false, P.orient_rep_chain _ hc (by simpa [flipChain] using hx'),
        P.orient_rep_chain _ hc (by simpa [flipChain] using hy')⟩
  · obtain ⟨_,b,hb⟩ := (P.closed_chain hc).chosen_rep hx
    obtain ⟨_,b',hb'⟩ := (P.closed_chain hc').chosen_rep hy
    let f : List V → Bool := fun d => if d = c then b else b'
    exact Or.inl ⟨f, P.orient_rep_chain f hc (by simpa [f] using hb),
      P.orient_rep_chain f hc' (by simpa [f, Ne.symm hcc] using hb')⟩

noncomputable def PathSystem.chosen {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : List V := (P.chains.map (chosenChain Q)).flatten

 theorem PathSystem.chosen_sublist {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.chosen.Sublist P.chains.flatten := by
  suffices hh : ∀ C : List (List V), (C.map (chosenChain Q)).flatten.Sublist C.flatten from hh P.chains
  intro C
  induction C with
  | nil => simp
  | cons c C ih =>
    simpa only [List.map_cons, List.flatten_cons] using (chosenChain_sublist Q c).append ih

 theorem PathSystem.chosen_count {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (hM : P.missing = ∅)
    (hA : ∃ A, AmountProfile P A ∧ ∀ a ∈ A, 2 ≤ a) :
    2 * Q.ncard ≤ P.chosen.length + P.amount := by
  classical
  obtain ⟨A, ⟨D,hD,hperm⟩, hAs⟩ := hA
  have hs : D.flatten.sum = P.amount := by
    rw [hperm.sum_eq]
    exact (AmountProfile.count ⟨D,hD,hperm⟩).1
  have hC1 : ∀ c ∈ P.chains, c.length ≠ 1 := by
    intro c hc he
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp he
    have hx : x ∈ P.missing := hc
    rw [hM] at hx
    exact hx
  have hh : ∀ (C : List (List V)) (D : List (List ℕ)), List.Forall₂ (ChainAmounts Q) C D →
      (∀ c ∈ C, c.length ≠ 1) → (∀ a ∈ D.flatten, 2 ≤ a) →
      (∀ c ∈ C, c.Nodup) → (∀ c ∈ C, ClosedChain G Q c) →
      2 * C.flatten.countP (fun x => decide (x ∈ Q)) ≤
      (C.map (chosenChain Q)).flatten.length + D.flatten.sum := by
    intro C D hD
    induction hD with
    | nil => simp
    | @cons c a C D hca hD ih =>
      intro hC1 hdall hnd hc
      have hb := (hc c (by simp)).chosen_count (hnd c (by simp)) hca
        (fun n hn => hdall n (List.mem_flatten.mpr ⟨a,by simp,hn⟩)) (hC1 c (by simp))
      have hi := ih (fun c hc => hC1 c (by simp [hc]))
        (fun n hn => hdall n (List.mem_flatten.mpr (by
          obtain ⟨a,ha,hna⟩ := List.mem_flatten.mp hn
          exact ⟨a,by simp [ha],hna⟩)))
        (fun c hc => hnd c (by simp [hc])) (fun c hc' => hc c (by simp [hc']))
      simp only [List.flatten_cons, List.countP_append, List.map_cons, List.length_append,
        List.sum_append]
      omega
  have hh' := hh P.chains D hD hC1 (fun a ha => hAs a (hperm.mem_iff.mp ha))
    (List.nodup_flatten.mp P.nodup).1 (fun c hc => P.closed_chain hc)
  simpa only [P.clique_count, hs, PathSystem.chosen] using hh'

 theorem OutsidePath.symm {V : Type*} {G : SimpleGraph V} {X : Set V} {x y : V} {d : ℕ}
    (h : OutsidePath G X x y d) : OutsidePath G X y x d := by
  obtain ⟨hx,hy,hxy,p,hp,hl,hs⟩ := h
  refine ⟨hy,hx,Ne.symm hxy,p.reverse,hp.reverse,by simpa using hl,?_⟩
  intro v hv hvX
  exact (hs v (by simpa using hv) hvX).symm

namespace LargeSystem
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V} {k : ℕ}
  {P : PathSystem G Q} (H : LargeSystem G Q k P)
include H

 theorem exclude_two_full (hL : P.amount + Q.ncard = k)
    (hA : ∃ A, AmountProfile P A ∧ ∀ a ∈ A, 2 ≤ a) (hM : P.missing = ∅) : False := by
  classical
  have hv : P.incident = Q.ncard := by
    have hh := P.incident_add_missing
    simpa only [hM, Set.ncard_empty, Nat.add_zero] using hh
  have hm : 2 * P.edgeCount ≤ P.amount := by
    obtain ⟨A,hA,ha⟩ := hA
    have hh := list_sum_lower A 2 ha
    simpa only [hA.count.1, hA.count.2.1] using hh
  have hk2 : 2 * Q.ncard ≤ k := by have := P.incident_le_twice_edgeCount; omega
  let F := P.chosen.toFinset
  have hmem : ∀ x ∈ F, ∃ c ∈ P.chains, x ∈ chosenChain Q c := by
    intro x hx
    obtain ⟨l,hl,hx⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hx)
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hl
    exact ⟨c,hc,hx⟩
  have hFX : ∀ x ∈ F, x ∈ P.vertices := by
    intro x hx
    exact P.chosen_sublist.subset (List.mem_toFinset.mp hx)
  have hno : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G P.vertices x y d := by
    intro x hx y hy hxy d hd hd6 hp
    obtain ⟨c,hc,hxc⟩ := hmem x hx
    obtain ⟨c',hc',hyc⟩ := hmem y hy
    have hxQ := (P.chosen_rep hc hxc).1
    rcases P.chosen_pair hc hc' hxc hyc hxy with ⟨f,hxr,hyr⟩ | ⟨u,v,he⟩ | ⟨u,v,he⟩
    · exact (H.orient f).no_short_interior hxr hyr hxQ d hd hd6 (by simpa using hp)
    · exact H.no_short_step hc [u] [v] (by simpa using he) d hd hd6 hp
    · exact H.no_short_step hc [u] [v] (by simpa using he) d hd hd6 hp.symm
  have hw : ∀ x ∈ F, 3 ≤ independence G (outsideBall G P.vertices x 2) := by
    intro x hx
    obtain ⟨c,hc,hxc⟩ := hmem x hx
    obtain ⟨_,f,hxr⟩ := P.chosen_rep hc hxc
    simpa using (H.orient f).second_triple hk2 hxr
  have hpack := packing_balls F (fun _ => 2) (fun _ => 3) hFX
    (fun x hx y hy hxy d hd hd6 => hno x hx y hy hxy d hd (by omega)) hw
  have hc : F.card = P.chosen.length := List.toFinset_card_of_nodup (P.chosen_sublist.nodup P.nodup)
  have hp : 3 * P.chosen.length ≤ k := by
    simpa only [Finset.sum_const, smul_eq_mul, hc, Nat.mul_comm] using hpack.trans H.independent
  have hn := P.chosen_count hM hA
  have ht := H.nine
  have hk := H.k_le
  omega

 theorem contradiction : False := by
  obtain ⟨x,hx,y,hy,d,hd,hd6,hp⟩ := H.short
  obtain ⟨hL,hA,hc⟩ := H.parameter hx hy (by omega) hd6 hp
  rcases hc with ⟨rfl,hv,_⟩ | ⟨rfl,hv,_⟩ | ⟨rfl,ht,hk,he,hv,_⟩
  · by_cases hM : P.missing.Nonempty
    · exact H.exclude_two_missing hL hA hv hM
    · exact H.exclude_two_full hL hA (Set.not_nonempty_iff_eq_empty.mp hM)
  · exact H.exclude_three hL hA hv
  · exact H.exclude_five ht hk hv

end LargeSystem

end CycleClique

namespace CycleClique
open scoped SimpleGraph

 

structure FiniteHyp {V : Type*} [Fintype V] (G : SimpleGraph V) (k t : ℕ) : Prop where
  hk : 5 ≤ k
  ht : 3 ≤ t
  htk : t ≤ k
  hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G
  hclique : G.cliqueNum ≤ t
  hα : G.indepNum ≤ k
  hexp : ∀ I : Set V, G.IsIndepSet I → I.Nonempty →
    k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard

namespace FiniteHyp
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k t : ℕ} (H : FiniteHyp G k t)
include H

theorem degree (x : V) : k + 1 ≤ (closedNeighborhood G {x}).ncard := by
  simpa using H.hexp {x} (by intro a ha b hb hab; simp_all) (Set.singleton_nonempty x)

theorem ball_zero_size {X Z : Set V} {x : V} (hx : x ∈ X) (hZ : Z ⊆ X)
    (hxZ : x ∉ Z) (hmiss : ∀ z ∈ Z, ¬ G.Adj x z) :
    k + 1 + Z.ncard ≤ X.ncard + (outsideBall G X x 0).ncard := by
  have hs : closedNeighborhood G {x} ⊆ outsideBall G X x 0 ∪ (X \ Z) := by
    rintro v (hv | ⟨u, hu, huv⟩)
    · have he : v = x := hv
      subst v
      exact Or.inr ⟨hx, hxZ⟩
    · have he : u = x := hu
      subst u
      by_cases hvX : v ∈ X
      · exact Or.inr ⟨hvX, fun hvZ => hmiss v hvZ huv⟩
      · exact Or.inl ⟨huv, hvX⟩
  have hc := Set.ncard_le_ncard hs
  have hu := Set.ncard_union_le (outsideBall G X x 0) (X \ Z)
  have hd := Set.ncard_sdiff_add_ncard_of_subset hZ
  have hh := H.degree x
  omega

theorem ball_zero_pair {X : Set V} {x : V} (hx : x ∈ X)
    (hb : t ≤ (outsideBall G X x 0).ncard) :
    2 ≤ independence G (outsideBall G X x 0) := by
  by_contra hn
  have hC := clique_of_independence_le_one (G := G) (S := outsideBall G X x 0) (by omega)
  have hCx : G.IsClique (insert x (outsideBall G X x 0)) := by
    intro u hu v hv huv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact (huv rfl).elim
    · exact hv.1
    · exact hu.1.symm
    · exact hC hu hv huv
  have hc := (clique_ncard_le_cliqueNum hCx).trans H.hclique
  rw [Set.ncard_insert_of_notMem (show x ∉ outsideBall G X x 0 from
    fun hh => hh.2 hx)] at hc
  omega

theorem ball_step_size {X Z : Set V} {x : V} {r u : ℕ}
    (hu : 1 ≤ u) (hweight : u ≤ independence G (outsideBall G X x r))
    (hZ : Z ⊆ X) (hmiss : ∀ v ∈ outsideBall G X x r, ∀ z ∈ Z, ¬ G.Adj v z) :
    k * u + 1 + Z.ncard ≤ X.ncard + (outsideBall G X x (r + 1)).ncard := by
  obtain ⟨I, hIs, hI, hIc⟩ := exists_indep_of_independence G (outsideBall G X x r)
  have hIn : I.Nonempty := (Set.ncard_pos).mp (by omega)
  have he := H.hexp I hI hIn
  have hb := outside_neighborhood_bound hIs hZ (fun v hv => hmiss v (hIs hv))
  have hm := Nat.mul_le_mul_left k (show u ≤ I.ncard by omega)
  omega

theorem ball_pair {X : Set V} {x : V} {r : ℕ}
    (hb : t < (outsideBall G X x r).ncard) :
    2 ≤ independence G (outsideBall G X x r) := by
  by_contra hn
  have hc := (clique_ncard_le_cliqueNum (clique_of_independence_le_one
    (G := G) (S := outsideBall G X x r) (by omega))).trans H.hclique
  omega

theorem ball_triple {X : Set V} {x : V} {r : ℕ}
    (hb : max k (2 * t) < (outsideBall G X x r).ncard) :
    3 ≤ independence G (outsideBall G X x r) :=
  size_test H.hk (by have := H.ht; omega) H.hcycle H.hclique _ hb

 
theorem ball_stagnation {X Z : Set V} {x : V} {r : ℕ}
    (hx : x ∈ X) (hZ : Z ⊆ X) (hxZ : x ∉ Z)
    (hb : t ≤ (outsideBall G X x r).ncard)
    (hnum : X.ncard + t ≤ k + 1 + Z.ncard)
    (hmiss : ∀ v ∈ outsideBall G X x r, ∀ z ∈ Z, ¬ G.Adj v z) :
    2 ≤ independence G (outsideBall G X x (r + 1)) := by
  by_contra hn
  have hC := clique_of_independence_le_one
    (G := G) (S := outsideBall G X x (r + 1)) (by omega)
  have hc := (clique_ncard_le_cliqueNum hC).trans H.hclique
  have hsub := outsideBall_subset_succ G X x r
  have hadj : ∀ v ∈ outsideBall G X x r, G.Adj x v := by
    intro v hv
    by_contra hneg
    have hZX : insert x Z ⊆ X := Set.insert_subset hx hZ
    have hm : ∀ u ∈ ({v} : Set V), ∀ z ∈ insert x Z, ¬ G.Adj u z := by
      intro u hu z hz huz
      have he : u = v := hu
      subst u
      rcases hz with rfl | hz
      · exact hneg huz.symm
      · exact hmiss v hv z hz huz
    have hh := outside_neighborhood_bound (Set.singleton_subset_iff.mpr hv) hZX hm
    rw [Set.ncard_insert_of_notMem hxZ] at hh
    have hd := H.degree v
    change (closedNeighborhood G {v}).ncard + (Z.ncard + 1) ≤
      X.ncard + (outsideBall G X x (r + 1)).ncard at hh
    omega
  have hbig : G.IsClique (insert x (outsideBall G X x r)) := by
    intro u hu v hv huv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact (huv rfl).elim
    · exact hadj v hv
    · exact (hadj u hu).symm
    · exact hC (hsub hu) (hsub hv) huv
  have hbigc := (clique_ncard_le_cliqueNum hbig).trans H.hclique
  rw [Set.ncard_insert_of_notMem (show x ∉ outsideBall G X x r from
    fun hh => outsideBall_subset_compl G X x r hh hx)] at hbigc
  omega

end FiniteHyp

 
def labelAdj (E : List (ℕ × ℕ)) (a b : ℕ) : Prop := (a,b) ∈ E ∨ (b,a) ∈ E
instance (E : List (ℕ × ℕ)) (a b : ℕ) : Decidable (labelAdj E a b) := by
  unfold labelAdj
  infer_instance

 
def LabelValid (n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ)) (C : List (List ℕ)) : Prop :=
  C.flatten.Nodup ∧ (∀ i ∈ C.flatten, i < n) ∧
  (∀ c ∈ C, c ≠ [] ∧ c.IsChain (labelAdj E) ∧
    c.IsChain (fun a b => a ∉ q ∨ b ∉ q) ∧
    (∀ x ∈ c.head?, x ∈ q) ∧ (∀ x ∈ c.getLast?, x ∈ q)) ∧
  ∀ i ∈ q, i ∈ C.flatten

instance (n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ)) (C : List (List ℕ)) :
    Decidable (LabelValid n q E C) := by
  unfold LabelValid
  infer_instance

structure LabelState {V : Type*} (G : SimpleGraph V) (Q : Set V)
    (n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ)) where
  f : ℕ → V
  inj : Set.InjOn f (Set.Iio n)
  qb : ∀ i ∈ q, i < n
  qimage : Q = f '' (↑q : Set ℕ)
  eb : ∀ a b, (a,b) ∈ E → a < n ∧ b < n
  edges : ∀ a b, labelAdj E a b → G.Adj (f a) (f b)

namespace LabelState
variable {V : Type*} {G : SimpleGraph V} {Q : Set V}
  {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)

def vertices : Set V := S.f '' Set.Iio n

theorem mem_vertices {i : ℕ} (hi : i < n) : S.f i ∈ S.vertices := ⟨i, hi, rfl⟩

theorem card_vertices : S.vertices.ncard = n := by
  rw [vertices, Set.InjOn.ncard_image S.inj, Set.ncard_Iio_nat]

include S in
theorem card_clique : Q.ncard = q.card := by
  rw [S.qimage, Set.InjOn.ncard_image (S.inj.mono S.qb), Set.ncard_coe_finset]

theorem mem_clique {i : ℕ} (hi : i < n) : S.f i ∈ Q ↔ i ∈ q := by
  constructor
  · intro hx
    have him : S.f i ∈ S.f '' (↑q : Set ℕ) := S.qimage ▸ hx
    obtain ⟨j, hj, he⟩ := him
    have hji := S.inj (S.qb j hj) hi he
    simpa only [hji, Finset.mem_coe] using hj
  · intro h
    exact Eq.mp (congrArg (fun A : Set V => S.f i ∈ A) S.qimage.symm)
      (show S.f i ∈ S.f '' (↑q : Set ℕ) from ⟨i, h, rfl⟩)

noncomputable def system {C : List (List ℕ)} (h : LabelValid n q E C) : PathSystem G Q := by
  classical
  refine {
    chains := C.map (List.map S.f)
    nonempty := ?_
    nodup := ?_
    edges := ?_
    positive := ?_
    ends := ?_
    cover := ?_ }
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    simpa using (h.2.2.1 a ha).1
  · rw [← List.map_flatten]
    exact h.1.map_on (fun a ha b hb he => S.inj (h.2.1 a ha) (h.2.1 b hb) he)
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    apply (List.isChain_map S.f).mpr
    exact (h.2.2.1 a ha).2.1.imp (fun {u v} huv => S.edges u v huv)
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    apply (List.isChain_map S.f).mpr
    apply (h.2.2.1 a ha).2.2.1.imp_of_mem_imp
    intro u v hu hv huv
    have hub := h.2.1 u (List.mem_flatten.mpr ⟨a, ha, hu⟩)
    have hvb := h.2.1 v (List.mem_flatten.mpr ⟨a, ha, hv⟩)
    simpa only [S.mem_clique hub, S.mem_clique hvb] using huv
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    constructor
    · intro x hx
      simp only [List.head?_map, Option.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact (S.mem_clique (S.qb i ((h.2.2.1 a ha).2.2.2.1 i hi))).mpr
        ((h.2.2.1 a ha).2.2.2.1 i hi)
    · intro x hx
      simp only [List.getLast?_map, Option.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact (S.mem_clique (S.qb i ((h.2.2.1 a ha).2.2.2.2 i hi))).mpr
        ((h.2.2.1 a ha).2.2.2.2 i hi)
  · intro x hx
    rw [S.qimage] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [← List.map_flatten]
    exact List.mem_map.mpr ⟨i, h.2.2.2 i hi, rfl⟩

@[simp] theorem system_chains {C : List (List ℕ)} (h : LabelValid n q E C) :
    (S.system h).chains = C.map (List.map S.f) := rfl

theorem system_amount [Fintype V] {C : List (List ℕ)} (h : LabelValid n q E C) :
    (S.system h).amount = C.flatten.length - q.card := by
  simp only [PathSystem.amount, S.system_chains, ← List.map_flatten, List.length_map, S.card_clique]

theorem system_edges [Fintype V] {C : List (List ℕ)} (h : LabelValid n q E C) :
    (S.system h).edgeCount = q.card - C.length := by
  simp only [PathSystem.edgeCount, S.system_chains, List.length_map, S.card_clique]

theorem system_incident [Fintype V] {C : List (List ℕ)} (h : LabelValid n q E C) :
    (S.system h).incident = q.card - (C.filter (fun c => c.length = 1)).length := by
  classical
  simp only [PathSystem.incident, PathSystem.singletons, S.system_chains, List.filter_map,
    Function.comp_def, List.length_map, S.card_clique]

end LabelState

end CycleClique

end OAI
