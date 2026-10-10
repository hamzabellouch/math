import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorPaths
import OAI.Combinatorics.Ramsey.CycleClique.MarkedChains
import OAI.Combinatorics.Ramsey.CycleClique.OptimalSystems
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

theorem PathSystem.vertices_ncard {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.vertices.ncard = Q.ncard + P.amount := by
  classical
  have he : P.vertices = (↑P.chains.flatten.toFinset : Set V) := by ext; simp
  rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup P.nodup, P.flat_length]

theorem OutsidePath.to_list {V : Type*} {G : SimpleGraph V} {X : Set V} {x y : V} {d : ℕ}
    (h : OutsidePath G X x y d) :
    ∃ I : List V, I.length = d ∧ (x :: I ++ [y]).IsChain G.Adj ∧
      I.Nodup ∧ ∀ a ∈ I, a ∉ X := by
  obtain ⟨hx, hy, hxy, p, hp, hlen, hs⟩ := h
  cases p with
  | nil => simp at hlen
  | cons hadj q =>
    let I := q.support.dropLast
    have he : q.support = I ++ [y] := by
      simpa only [I, q.getLast_support] using (List.dropLast_concat_getLast q.support_ne_nil).symm
    have hn : (x :: I ++ [y]).Nodup := by
      simpa only [SimpleGraph.Walk.support_cons, he, List.cons_append] using hp.support_nodup
    have htail := (List.nodup_cons.mp hn).2
    have hi := (List.nodup_append.mp htail).1
    have hxI : x ∉ I := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
    have hyI : y ∉ I := fun hy => (List.nodup_append.mp htail).2.2 y hy y (by simp) rfl
    refine ⟨I, ?_, ?_, hi, ?_⟩
    · have hl := q.length_support
      rw [he, List.length_append, List.length_singleton] at hl
      simp only [SimpleGraph.Walk.length_cons] at hlen
      omega
    · simpa only [SimpleGraph.Walk.support_cons, he, List.cons_append] using
        (SimpleGraph.Walk.cons hadj q).isChain_adj_support
    · intro a ha haX
      rcases hs a (by simp only [SimpleGraph.Walk.support_cons, he, List.mem_cons,
        List.mem_append]; exact Or.inr (Or.inl ha)) haX with rfl | rfl
      · exact hxI ha
      · exact hyI ha

theorem positive_interior_chain {V : Type*} {Q : Set V} {x y : V} {I : List V}
    (hne : I ≠ []) (hout : ∀ a ∈ I, a ∉ Q) :
    (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) := by
  induction I generalizing x with
  | nil => contradiction
  | cons a I ih =>
    have ha := hout a (by simp)
    apply List.isChain_cons.mpr
    constructor
    · intro b hb
      have he : a = b := by simpa using hb
      exact Or.inr (he ▸ ha)
    · cases I with
      | nil => simpa using (Or.inl ha : a ∉ Q ∨ y ∉ Q)
      | cons b I =>
        exact ih (by simp) (fun c hc => hout c (by simp [hc]))

theorem PathSystem.no_one_representatives {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hk : 3 ≤ k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (ht : Q.ncard ≤ k)
    {x y : V} (hx : x ∈ P.reps) (hy : y ∈ P.reps) :
    ¬ OutsidePath G P.vertices x y 1 := by
  intro hp
  obtain ⟨I, hIl, hI, hIn, hIo⟩ := hp.to_list
  have hip : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) :=
    positive_interior_chain (by intro h; simp [h] at hIl)
      (fun a ha hQ => hIo a ha (P.cover a hQ))
  have hid : I.Disjoint P.chains.flatten := List.disjoint_left.mpr hIo
  obtain ⟨R, hR⟩ := P.representative_replacement hx hy hp.2.2.1 I hI hip hIn hid
  have hr : R.incident ≤ Q.ncard := Nat.sub_le _ _
  have hh := hopt.1
  apply P.optimality hopt hk hQ hcycle ht R (by omega) (by omega)
  omega

theorem isChain_insert_step {V : Type*} {R : V → V → Prop} {A I B : List V} {x y : V}
    (hc : (A ++ x :: y :: B).IsChain R) (hI : (x :: I ++ [y]).IsChain R) :
    (A ++ x :: I ++ y :: B).IsChain R := by
  have hp : (A ++ [x]).IsChain R := by
    apply List.IsChain.left_of_append (l₂ := y :: B)
    simpa only [List.append_assoc, List.singleton_append] using hc
  have hs : (y :: B).IsChain R := by
    apply List.IsChain.right_of_append (l₁ := A ++ [x])
    simpa only [List.append_assoc, List.singleton_append] using hc
  have h₁ : (A ++ [x] ++ (I ++ [y])).IsChain R := hp.append_overlap hI (by simp)
  have h₂ : (A ++ [x] ++ I ++ [y] ++ B).IsChain R :=
    (show (A ++ [x] ++ I ++ [y]).IsChain R by simpa only [List.append_assoc] using h₁).append_overlap
      hs (by simp)
  simpa only [List.append_assoc, List.singleton_append] using h₂

theorem PathSystem.insert_step {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c : List V} (hc : c ∈ P.chains) {x y : V} (A I B : List V)
    (he : c = A ++ x :: y :: B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧ R.edgeCount = P.edgeCount := by
  classical
  let D := P.chains.erase c
  let J := A ++ x :: I ++ y :: B
  have hp : P.chains.Perm (c :: D) := List.perm_cons_erase hc
  have hj : (J ++ D.flatten).Perm (I ++ P.chains.flatten) := by
    apply List.Perm.trans _ (hp.flatten.symm.append_left I)
    simp only [List.flatten_cons, he, J]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]
    ac_nf
    exact Multiset.cons_swap ..
  have hnd : (J ++ D.flatten).Nodup := hj.nodup_iff.mpr
    (List.nodup_append.mpr ⟨hIn, P.nodup, fun a ha b hb hab =>
      List.disjoint_left.mp hId ha (hab ▸ hb)⟩)
  have hje : (∀ a ∈ J.head?, a ∈ Q) ∧ ∀ a ∈ J.getLast?, a ∈ Q := by
    have hh := P.ends c hc
    constructor
    · simpa only [he, J, List.append_assoc, List.cons_append, List.head?_append, List.head?_cons] using hh.1
    · have hec : c = (A ++ [x]) ++ y :: B := by simp only [he, List.append_assoc, List.singleton_append]
      have hej : J = (A ++ [x] ++ I) ++ y :: B := by
        simp only [J, List.append_assoc, List.cons_append, List.nil_append]
      simpa only [hec, hej, List.getLast?_append_of_ne_nil _ (by simp : y :: B ≠ [])] using hh.2
  let R : PathSystem G Q :=
    { chains := J :: D
      nonempty := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · simp [J]
        · exact P.nonempty d (List.mem_of_mem_erase hd)
      nodup := hnd
      edges := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact isChain_insert_step (he ▸ P.edges c hc) hI
        · exact P.edges d (List.mem_of_mem_erase hd)
      positive := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact isChain_insert_step (he ▸ P.positive c hc) hIp
        · exact P.positive d (List.mem_of_mem_erase hd)
      ends := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact hje
        · exact P.ends d (List.mem_of_mem_erase hd)
      cover := by
        intro a ha
        exact hj.mem_iff.mpr (List.mem_append_right _ (P.cover a ha)) }
  refine ⟨R, ?_, ?_⟩
  · have hh := hj.length_eq
    simp only [List.length_append, P.flat_length] at hh
    change (J ++ D.flatten).length - Q.ncard = P.amount + I.length
    rw [List.length_append]
    omega
  · have hh := hp.length_eq
    change Q.ncard - (J :: D).length = Q.ncard - P.chains.length
    simp only [List.length_cons] at hh ⊢
    omega

theorem PathSystem.no_one_consecutive {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hk : 3 ≤ k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (ht : Q.ncard ≤ k)
    {c : List V} (hc : c ∈ P.chains) {x y : V} (A B : List V)
    (he : c = A ++ x :: y :: B) :
    ¬ OutsidePath G P.vertices x y 1 := by
  intro hp
  obtain ⟨I, hIl, hI, hIn, hIo⟩ := hp.to_list
  have hip : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) :=
    positive_interior_chain (by intro h; simp [h] at hIl)
      (fun a ha hQ => hIo a ha (P.cover a hQ))
  obtain ⟨R, hR, _⟩ := P.insert_step hc A I B he hI hip hIn (List.disjoint_left.mpr hIo)
  have hr : R.incident ≤ Q.ncard := Nat.sub_le _ _
  have hh := hopt.1
  apply P.optimality hopt hk hQ hcycle ht R (by omega) (by omega)
  omega

abbrev PathSystem.representatives {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : Set V := {v | v ∈ P.reps}

theorem PathSystem.representatives_ncard {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.representatives.ncard = Q.ncard := by
  classical
  have he : P.representatives = (↑P.reps.toFinset : Set V) := by ext; simp
  rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup (P.nodup.sublist P.reps_sublist),
    P.reps_length]

end CycleClique

end OAI
