import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.MarkedChains
import OAI.Combinatorics.Ramsey.CycleClique.OptimalSystems
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

inductive ChainAmounts {V : Type*} (Q : Set V) : List V → List ℕ → Prop
  | singleton (x : V) (hx : x ∈ Q) : ChainAmounts Q [x] []
  | step (x y : V) (I B : List V) (A : List ℕ) (hx : x ∈ Q)
      (hI : I ≠ []) (hout : ∀ z ∈ I, z ∉ Q)
      (tail : ChainAmounts Q (y :: B) A) :
      ChainAmounts Q (x :: (I ++ y :: B)) (I.length :: A)

theorem first_mem_split {V : Type*} (Q : Set V) (c : List V)
    (h : ∃ x ∈ c, x ∈ Q) :
    ∃ I x B, c = I ++ x :: B ∧ (∀ z ∈ I, z ∉ Q) ∧ x ∈ Q := by
  classical
  induction c with
  | nil => simp at h
  | cons x c ih =>
    by_cases hx : x ∈ Q
    · exact ⟨[], x, c, rfl, by simp, hx⟩
    · have ht : ∃ y ∈ c, y ∈ Q := by
        obtain ⟨y, hy, hyQ⟩ := h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (hx hyQ).elim
        · exact ⟨y, hy, hyQ⟩
      obtain ⟨I, y, B, he, hout, hy⟩ := ih ht
      refine ⟨x :: I, y, B, ?_, ?_, hy⟩
      · simp only [he, List.cons_append]
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact hout z hz

theorem ChainAmounts.exists {V : Type*} {Q : Set V} {G : SimpleGraph V}
    (c : List V) (hc : ClosedChain G Q c) : ∃ A, ChainAmounts Q c A := by
  cases c with
  | nil => exact (hc.nonempty rfl).elim
  | cons x l =>
    have hx : x ∈ Q := hc.ends.1 x (by simp)
    by_cases hl : l = []
    · subst l
      exact ⟨[], .singleton x hx⟩
    · have hh : ∃ y ∈ l, y ∈ Q := by
        refine ⟨l.getLast hl, List.getLast_mem hl, ?_⟩
        apply hc.ends.2
        simpa only [List.getLast?_cons_of_ne_nil hl, List.getLast?_eq_some_getLast hl] using
          (Option.mem_def.mpr rfl : l.getLast hl ∈ some (l.getLast hl))
      obtain ⟨I, y, B, he, hout, hy⟩ := first_mem_split Q l hh
      have hec : x :: l = (x :: I) ++ y :: B := by simp [he]
      have hI : I ≠ [] := by
        intro hi
        subst I
        have hp := hc.positive
        rw [he] at hp
        exact hp.rel.elim (fun h => h hx) (fun h => h hy)
      have ht : ClosedChain G Q (y :: B) := {
        nonempty := by simp
        edges := by rw [hec] at hc; exact hc.edges.right_of_append
        positive := by rw [hec] at hc; exact hc.positive.right_of_append
        ends := ⟨by simpa using hy, by
          simpa only [hec, List.getLast?_append_of_ne_nil _ (by simp : y :: B ≠ [])] using hc.ends.2⟩ }
      obtain ⟨A, hA⟩ := ChainAmounts.exists (y :: B) ht
      exact ⟨I.length :: A, by simpa only [he] using ChainAmounts.step x y I B A hx hI hout hA⟩
termination_by c.length

 theorem ChainAmounts.head_mem {V : Type*} {Q : Set V} {c : List V} {A : List ℕ}
    (h : ChainAmounts Q c A) : ∀ x ∈ c.head?, x ∈ Q := by
  cases h <;> simp_all

theorem ChainAmounts.count {V : Type*} {Q : Set V} {c : List V} {A : List ℕ}
    (h : ChainAmounts Q c A) :
    c.countP (fun v => decide (v ∈ Q)) = A.length + 1 ∧
    c.length = A.sum + A.length + 1 ∧ ∀ a ∈ A, 1 ≤ a := by
  classical
  induction h with
  | singleton x hx => simp [hx]
  | step x y I B A hx hI hout htail ih =>
    have hcI : I.countP (fun v => decide (v ∈ Q)) = 0 := by
      apply List.countP_eq_zero.mpr
      simpa using hout
    have hi : 1 ≤ I.length := List.length_pos_iff.mpr hI
    rcases ih with ⟨hc, hl, hp⟩
    constructor
    · simp only [List.countP_cons, List.countP_append, hcI, hx, decide_true,
        ite_true, List.length_cons] at hc ⊢
      omega
    constructor
    · simp only [List.length_cons, List.length_append, List.sum_cons] at hl ⊢
      omega
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hi
      · exact hp a ha

theorem ChainAmounts.deletion_split {V : Type*} {Q : Set V} {c : List V} {A : List ℕ}
    (h : ChainAmounts Q c A) {a : ℕ} (ha : a ∈ A) :
    ∃ U x I y B AL AR, c = U ++ x :: (I ++ y :: B) ∧ I.length = a ∧
      (∀ z ∈ I, z ∉ Q) ∧ ChainAmounts Q (U ++ [x]) AL ∧
      ChainAmounts Q (y :: B) AR ∧ A = AL ++ a :: AR := by
  induction h with
  | singleton x hx => simp at ha
  | step p q J C A hp hJ hJout htail ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨[], p, J, q, C, [], A, rfl, rfl, hJout, .singleton p hp, htail, rfl⟩
    · obtain ⟨U, x, I, y, B, AL, AR, he, hi, hout, hleft, hright, hA⟩ := ih ha
      have hne : U ++ [x] ≠ [] := by simp
      obtain ⟨q', D, hD⟩ := List.exists_cons_of_ne_nil hne
      have hq : q' = q := by
        have hh := congrArg List.head? he
        have hh' := congrArg List.head? hD
        cases U <;> simp_all
      subst q'
      have hleft' : ChainAmounts Q ((p :: (J ++ U)) ++ [x]) (J.length :: AL) := by
        have hc := ChainAmounts.step p q J D AL hp hJ hJout (hD ▸ hleft)
        simpa only [← hD, List.append_assoc, List.cons_append] using hc
      refine ⟨p :: (J ++ U), x, I, y, B, J.length :: AL, AR, ?_, hi, hout,
        hleft', hright, ?_⟩
      · rw [he]
        simp only [List.append_assoc, List.cons_append]
      · simp only [hA, List.cons_append]

 
def AmountProfile {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (A : List ℕ) : Prop :=
  ∃ blocks : List (List ℕ), List.Forall₂ (ChainAmounts Q) P.chains blocks ∧ blocks.flatten.Perm A

theorem PathSystem.exists_profile {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : ∃ A, AmountProfile P A := by
  have hh : ∀ c ∈ P.chains, ∃ A, ChainAmounts Q c A :=
    fun c hc => ChainAmounts.exists c (P.closed_chain hc)
  have hex : ∃ D, List.Forall₂ (ChainAmounts Q) P.chains D := by
    generalize P.chains = C at hh ⊢
    revert hh
    induction C with
    | nil => intro _; exact ⟨[], .nil⟩
    | cons c C ih =>
      intro hh
      obtain ⟨A, hA⟩ := hh c (by simp)
      obtain ⟨D, hD⟩ := ih (fun d hd => hh d (by simp [hd]))
      exact ⟨A :: D, .cons hA hD⟩
  obtain ⟨D, hD⟩ := hex
  exact ⟨D.flatten, ⟨D, hD, List.Perm.refl _⟩⟩

theorem AmountProfile.count {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A : List ℕ} (h : AmountProfile P A) :
    A.sum = P.amount ∧ A.length = P.edgeCount ∧ ∀ a ∈ A, 1 ≤ a := by
  obtain ⟨D, hD, hperm⟩ := h
  have hh : P.chains.flatten.countP (fun x => decide (x ∈ Q)) = D.flatten.length + P.chains.length ∧
      P.chains.flatten.length = D.flatten.sum + D.flatten.length + P.chains.length ∧
      ∀ a ∈ D.flatten, 1 ≤ a := by
    clear hperm
    generalize P.chains = C at hD ⊢
    induction hD with
    | nil => simp
    | @cons c B C D hc hC ih =>
      obtain ⟨hq, hl, hp⟩ := hc.count
      rcases ih with ⟨hq', hl', hp'⟩
      constructor
      · simp only [List.flatten_cons, List.countP_append, List.length_append, List.length_cons]
        omega
      constructor
      · simp only [List.flatten_cons, List.length_append, List.sum_append, List.length_cons]
        omega
      · intro a ha
        simp only [List.flatten_cons, List.mem_append] at ha
        exact ha.elim (hp a) (hp' a)
  rw [P.clique_count, P.flat_length, hperm.length_eq, hperm.sum_eq] at hh
  dsimp [PathSystem.edgeCount]
  exact ⟨by omega, by omega, fun a ha => hh.2.2 a (hperm.mem_iff.mpr ha)⟩

theorem AmountProfile.perm {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A B : List ℕ} (h : AmountProfile P A) (hp : A.Perm B) :
    AmountProfile P B := by
  obtain ⟨D, hD, hDA⟩ := h
  exact ⟨D, hD, hDA.trans hp⟩

theorem ChainAmounts.ends {V : Type*} {Q : Set V} {c : List V} {A : List ℕ}
    (h : ChainAmounts Q c A) :
    (∀ x ∈ c.head?, x ∈ Q) ∧ ∀ y ∈ c.getLast?, y ∈ Q := by
  induction h with
  | singleton x hx => simpa using And.intro hx hx
  | step x y I B A hx hI hout htail ih =>
    constructor
    · simpa using hx
    · simpa only [show x :: (I ++ y :: B) = (x :: I) ++ y :: B from by simp,
        List.getLast?_append_of_ne_nil _ (by simp : y :: B ≠ [])] using ih.2

theorem forall₂_select_right {α β : Type*} {R : α → β → Prop}
    {C : List α} {D : List β} (h : List.Forall₂ R C D) {b : β} (hb : b ∈ D) :
    ∃ C₁ c C₂ D₁ D₂, C = C₁ ++ c :: C₂ ∧ D = D₁ ++ b :: D₂ ∧
      List.Forall₂ R C₁ D₁ ∧ R c b ∧ List.Forall₂ R C₂ D₂ := by
  induction h with
  | nil => simp at hb
  | @cons c d C D hcd hCD ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨[], c, C, [], D, rfl, rfl, .nil, hcd, hCD⟩
    · obtain ⟨C₁, c', C₂, D₁, D₂, hC, hD, hpre, hcc, hpost⟩ := ih hb
      exact ⟨c :: C₁, c', C₂, d :: D₁, D₂,
        by simp [hC], by simp [hD], .cons hcd hpre, hcc, hpost⟩

theorem AmountProfile.delete {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A : List ℕ} (h : AmountProfile P A) {a : ℕ} (ha : a ∈ A) :
    ∃ R : PathSystem G Q, ∃ B : List ℕ, AmountProfile R B ∧ (a :: B).Perm A := by
  obtain ⟨D, hD, hDA⟩ := h
  obtain ⟨C, hCD, haC⟩ := List.mem_flatten.mp (hDA.mem_iff.mpr ha)
  obtain ⟨CP, c, CS, DP, DS, hP, hD', hpre, hcC, hpost⟩ := forall₂_select_right hD hCD
  obtain ⟨U, x, I, y, B, AL, AR, he, hIa, hIo, hleft, hright, hC⟩ := hcC.deletion_split haC
  let J := U ++ [x]
  let K := y :: B
  let newC := CP ++ J :: K :: CS
  let newD := DP ++ AL :: AR :: DS
  have hec : c = J ++ I ++ K := by simpa only [J, K, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using he
  have hperm : (I ++ newC.flatten).Perm P.chains.flatten := by
    rw [hP]
    dsimp [newC]
    simp only [List.flatten_append, List.flatten_cons, hec]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  have hnd := List.nodup_append.mp (hperm.nodup_iff.mpr P.nodup)
  have hcc := P.closed_chain (by rw [hP]; simp : c ∈ P.chains)
  have hj : ClosedChain G Q J := {
    nonempty := by simp [J]
    edges := by rw [hec] at hcc; exact hcc.edges.left_of_append.left_of_append
    positive := by rw [hec] at hcc; exact hcc.positive.left_of_append.left_of_append
    ends := hleft.ends }
  have hk : ClosedChain G Q K := {
    nonempty := by simp [K]
    edges := by rw [hec] at hcc; exact hcc.edges.right_of_append
    positive := by rw [hec] at hcc; exact hcc.positive.right_of_append
    ends := hright.ends }
  have holds : ∀ l ∈ newC, ClosedChain G Q l := by
    intro l hl
    simp only [newC, List.mem_append, List.mem_cons] at hl
    rcases hl with hl | rfl | rfl | hl
    · exact P.closed_chain (by rw [hP]; simp [hl])
    · exact hj
    · exact hk
    · exact P.closed_chain (by rw [hP]; simp [hl])
  let R : PathSystem G Q := {
    chains := newC
    nonempty := fun l hl => (holds l hl).nonempty
    nodup := hnd.2.1
    edges := fun l hl => (holds l hl).edges
    positive := fun l hl => (holds l hl).positive
    ends := fun l hl => (holds l hl).ends
    cover := by
      intro v hv
      have hv' := hperm.mem_iff.mpr (P.cover v hv)
      rcases List.mem_append.mp hv' with hvi | hvn
      · exact (hIo v hvi hv).elim
      · exact hvn }
  have hd : List.Forall₂ (ChainAmounts Q) R.chains newD :=
    List.rel_append hpre (.cons hleft (.cons hright hpost))
  refine ⟨R, newD.flatten, ⟨newD, hd, List.Perm.refl _⟩, ?_⟩
  apply List.Perm.trans _ hDA
  rw [hD', hC]
  dsimp [newD]
  simp only [List.flatten_append, List.flatten_cons]
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]
  ac_rfl

theorem AmountProfile.erase {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A : List ℕ} (h : AmountProfile P A) {a : ℕ} (ha : a ∈ A) :
    ∃ R : PathSystem G Q, AmountProfile R (A.erase a) := by
  obtain ⟨R, B, hB, hp⟩ := h.delete ha
  have he : (a :: B).Perm (a :: A.erase a) := hp.trans (List.perm_cons_erase ha)
  exact ⟨R, hB.perm (List.Perm.cons_inv he)⟩

theorem AmountProfile.drop_prefix {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    (C B : List ℕ) {P : PathSystem G Q} (h : AmountProfile P (C ++ B)) :
    ∃ R : PathSystem G Q, AmountProfile R B := by
  induction C generalizing P with
  | nil => exact ⟨P, h⟩
  | cons a C ih =>
    obtain ⟨R, hR⟩ := h.erase (by simp : a ∈ (a :: C) ++ B)
    have hr : AmountProfile R (C ++ B) := by simpa using hR
    exact ih hr

theorem AmountProfile.prune {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A B : List ℕ} (h : AmountProfile P A) (hB : B.Sublist A) :
    ∃ R : PathSystem G Q, AmountProfile R B := by
  obtain ⟨C, hAC⟩ := hB.exists_perm_append
  exact (h.perm (hAC.trans (List.perm_append_comm))).drop_prefix C B

theorem PathSystem.incident_le_twice_edgeCount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.incident ≤ 2 * P.edgeCount := by
  classical
  have hb : ∀ c ∈ P.chains,
      2 ≤ c.countP (fun v => decide (v ∈ Q)) + if c.length = 1 then 1 else 0 := by
    intro c hc
    obtain ⟨A, hA⟩ := ChainAmounts.exists c (P.closed_chain hc)
    have hh := hA.count
    by_cases he : c.length = 1
    · simp only [he, ite_true]
      omega
    · simp only [he, ite_false]
      have hn : A.length ≠ 0 := by
        intro hn
        have heA : A = [] := List.length_eq_zero_iff.mp hn
        simp only [heA, List.sum_nil, List.length_nil] at hh
        omega
      omega
  have hs := List.sum_le_sum hb
  have he : (P.chains.map (fun c =>
      c.countP (fun v => decide (v ∈ Q)) + if c.length = 1 then 1 else 0)).sum =
      Q.ncard + P.singletons.length := by
    rw [List.sum_map_add, ← List.countP_flatten, P.clique_count]
    congr 1
    simp only [PathSystem.singletons, ← List.countP_eq_length_filter]
    induction P.chains with
    | nil => simp
    | cons c C ih =>
      simp only [List.map_cons, List.sum_cons, List.countP_cons, decide_eq_true_eq]
      omega
  rw [he] at hs
  have hh := P.chains_length_le
  have hss := P.singletons_length_le
  have hleft : (P.chains.map (fun _ => 2)).sum = 2 * P.chains.length := by simp [Nat.mul_comm]
  rw [hleft] at hs
  dsimp [PathSystem.incident, PathSystem.edgeCount]
  omega

theorem ChainAmounts.run_bound {V : Type*} {Q : Set V} {c I : List V} {A : List ℕ}
    (h : ChainAmounts Q c A) (hI : I ≠ []) (hout : ∀ z ∈ I, z ∉ Q)
    (hin : I <:+: c) : ∃ a ∈ A, I.length ≤ a := by
  induction h with
  | singleton x hx =>
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil I hI
    have he : z = x := by simpa using hin.sublist.subset hz
    subst z
    exact (hout x hz hx).elim
  | step x y J B A hx hJ hJo htail ih =>
    have hy : y ∈ Q := htail.head_mem y (by simp)
    have hin' : I <:+: (x :: J) ++ y :: B := by simpa only [List.cons_append] using hin
    rcases List.infix_append_iff_ne_nil.mp hin' with hleft | hright | ⟨I₁, I₂, hn₁, hn₂, he, hs, hp⟩
    · have hh : I.Sublist J := by
        rcases List.sublist_cons_iff.mp hleft.sublist with h | ⟨D, hd, _⟩
        · exact h
        · exact (hout x (by simp [hd]) hx).elim
      exact ⟨J.length, by simp, hh.length_le⟩
    · obtain ⟨a, ha, hIa⟩ := ih hright
      exact ⟨a, by simp [ha], hIa⟩
    · obtain ⟨z, Z, hz⟩ := List.exists_cons_of_ne_nil hn₂
      obtain ⟨T, hT⟩ := hp
      rw [hz] at hT
      have hzy : z = y := (List.cons.inj hT).1
      subst z
      have hyI : y ∈ I := by rw [he, hz]; simp
      exact (hout y hyI hy).elim

theorem AmountProfile.run_bound {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A : List ℕ} (h : AmountProfile P A)
    {c I : List V} (hc : c ∈ P.chains) (hI : I ≠ []) (hout : ∀ z ∈ I, z ∉ Q)
    (hin : I <:+: c) : ∃ a ∈ A, I.length ≤ a := by
  obtain ⟨D, hD, hDA⟩ := h
  obtain ⟨DP, B, DS, CP, CS, hDs, _, _, hBc, _⟩ := forall₂_select_right hD.flip hc
  obtain ⟨a, ha, hIa⟩ := ChainAmounts.run_bound hBc hI hout hin
  refine ⟨a, hDA.mem_iff.mp ?_, hIa⟩
  exact List.mem_flatten.mpr ⟨B, by rw [hDs]; simp, ha⟩

theorem list_minimal_above (A : List ℕ) (h : ℕ) (hh : h ≤ A.sum) :
    ∃ B : List ℕ, B.Sublist A ∧ h ≤ B.sum ∧ ∀ a ∈ B, (B.erase a).sum < h := by
  let E : ℕ → Prop := fun n => ∃ B : List ℕ, B.Sublist A ∧ h ≤ B.sum ∧ B.length = n
  have hex : ∃ n, E n := ⟨A.length, A, .refl _, hh, rfl⟩
  obtain ⟨B, hB, hb, hn⟩ := Nat.find_spec hex
  refine ⟨B, hB, hb, ?_⟩
  intro a ha
  by_contra! he
  have hm := Nat.find_min' hex (show E (B.erase a).length from
    ⟨B.erase a, (List.erase_sublist).trans hB, he, rfl⟩)
  have hl := List.length_erase_add_one ha
  omega

theorem list_sum_erase {A : List ℕ} {a : ℕ} (ha : a ∈ A) :
    A.sum = a + (A.erase a).sum := by
  simpa using (List.perm_cons_erase ha).sum_eq

theorem list_sum_lower (A : List ℕ) (b : ℕ) (h : ∀ a ∈ A, b ≤ a) :
    b * A.length ≤ A.sum := by
  have hh := List.sum_le_sum h
  simpa [Nat.mul_comm] using hh

theorem increment_numeric {t L r j s : ℕ} (ht : 9 ≤ t) (hL : L ≤ t + 1)
    (hwr : t + 1 ≤ 2 * r + j) (hj1 : 1 ≤ j) (hj5 : j ≤ 5)
    (hs : s + 1 = r) (hb : (j + 2) * s ≤ L) : False := by
  interval_cases j <;> nlinarith

 

theorem PathSystem.small_increment {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k d : ℕ} (P R : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    (hd : 1 ≤ d) (hd6 : d ≤ 6) (hR : R.amount = P.amount + d)
    (he : R.edgeCount ≤ P.edgeCount + 1) {A : List ℕ}
    (hA : AmountProfile R A) {b : ℕ} (hb : b ∈ A) (hbd : d ≤ b) :
    P.amount = k - Q.ncard ∧ R.edgeCount = P.edgeCount + 1 ∧
      2 ≤ d ∧ ∀ a ∈ A, d ≤ a := by
  let h := k + 1 - Q.ncard
  have hL : P.amount < h := hopt.1
  have hh : h ≤ R.amount := by
    by_contra! hh
    have hx := hopt.2.1 R hh
    omega
  obtain ⟨hsum, hlen, hpos⟩ := hA.count
  obtain ⟨B, hBA, hBh, hBmin⟩ := list_minimal_above A h (by omega)
  obtain ⟨T, hT⟩ := hA.prune hBA
  obtain ⟨hTS, hTL, hTP⟩ := hT.count
  have hsumB : B.sum ≤ A.sum := hBA.sum_le_sum (fun _ _ => Nat.zero_le _)
  have hlengthB : B.length ≤ A.length := hBA.length_le
  have hEr : (A.erase b).sum ≤ P.amount := by
    have hs := list_sum_erase hb
    omega
  have hbB : b ∈ B := by
    by_contra hbB
    have hs := (hBA.erase b).sum_le_sum (fun _ _ => Nat.zero_le _)
    rw [List.erase_of_not_mem hbB] at hs
    omega
  have hsumEr : (B.erase b).sum ≤ P.amount :=
    le_trans ((hBA.erase b).sum_le_sum (fun _ _ => Nat.zero_le _)) hEr
  let j := B.sum - h
  have hj : B.sum = h + j := by dsimp [j]; omega
  have hj5 : j ≤ 5 := by omega
  have hwi := T.incident_le_twice_edgeCount
  have hwt : T.incident ≤ Q.ncard := Nat.sub_le _ _
  have hw : k + 1 - T.incident < T.amount := by
    by_contra! hw
    exact T.closing_interval (by omega) hQ hcycle htk (by omega) hw
  have hj1 : 1 ≤ j := by dsimp [h] at hj; omega
  have hwr : Q.ncard + 1 ≤ 2 * B.length + j := by dsimp [h] at hj; omega
  have hsmall : ∃ a ∈ B, a = j + 1 := by
    by_contra! hn
    have hge : ∀ a ∈ B, j + 2 ≤ a := by
      intro a ha
      have hm := hBmin a ha
      have hs := list_sum_erase ha
      have hne := hn a ha
      omega
    have hbg := list_sum_lower (B.erase b) (j + 2)
      (fun a ha => hge a (List.mem_of_mem_erase ha))
    have hbl := List.length_erase_add_one hbB
    have hLt : P.amount ≤ Q.ncard + 1 := by dsimp [h] at hL; omega
    exact increment_numeric ht hLt hwr hj1 hj5 hbl (le_trans hbg hsumEr)
  obtain ⟨a, ha, har⟩ := hsmall
  obtain ⟨U, hU⟩ := hT.erase ha
  have hcU := hU.count
  have hSU := list_sum_erase ha
  have hLU := List.length_erase_add_one ha
  have hUamount : U.amount = h - 1 := by omega
  have hUL : U.amount ≤ P.amount := hopt.2.1 U (by dsimp [h] at *; omega)
  have hLeq : P.amount = k - Q.ncard := by dsimp [h] at *; omega
  have hULeq : U.amount = P.amount := by dsimp [h] at *; omega
  have hUE := hopt.2.2 U hULeq
  have heq : R.edgeCount = P.edgeCount + 1 := by omega
  have hBEq : B = A := hBA.eq_of_length (by omega)
  subst B
  have hjd : j + 1 = d := by dsimp [h] at hj; omega
  refine ⟨hLeq, heq, by omega, ?_⟩
  intro a ha
  have hm := hBmin a ha
  have hs := list_sum_erase ha
  omega

theorem PathSystem.join_tails_exact {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    (C : List (List V)) {x y : V} (u v I : List V)
    (hperm : ((x :: u) ++ (y :: v) ++ C.flatten).Perm P.chains.flatten)
    (hne : ∀ c ∈ C, c ≠ []) (hc : ∀ c ∈ C, c.IsChain G.Adj)
    (hcp : ∀ c ∈ C, c.IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hce : ∀ c ∈ C, (∀ a ∈ c.head?, a ∈ Q) ∧ (∀ a ∈ c.getLast?, a ∈ Q))
    (hu : (x :: u).IsChain G.Adj) (hv : (y :: v).IsChain G.Adj)
    (hup : (x :: u).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hvp : (y :: v).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hue : ∀ a ∈ (x :: u).getLast?, a ∈ Q)
    (hve : ∀ a ∈ (y :: v).getLast?, a ∈ Q)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧ R.chains = ((x :: u).reverse ++ I ++ (y :: v)) :: C := by
  classical
  let J := (x :: u).reverse ++ I ++ (y :: v)
  have hJn : J ≠ [] := by simp [J]
  have hnd : (J ++ C.flatten).Nodup := by
    apply nodup_bridge (hperm.nodup_iff.mpr P.nodup) hIn
    apply List.disjoint_left.mpr
    intro a ha hb
    exact List.disjoint_left.mp hId ha (hperm.subset hb)
  have hJe : (∀ a ∈ J.head?, a ∈ Q) ∧ (∀ a ∈ J.getLast?, a ∈ Q) := by
    constructor
    · intro a ha
      apply hue a
      simpa only [J, List.append_assoc, List.head?_append_of_ne_nil _ (by simp : (x :: u).reverse ≠ []),
        List.head?_reverse] using ha
    · intro a ha
      apply hve a
      simpa only [J, ← List.append_assoc,
        List.getLast?_append_of_ne_nil _ (by simp : y :: v ≠ [])] using ha
  let R : PathSystem G Q :=
    { chains := J :: C
      nonempty := by intro c hc; simp only [List.mem_cons] at hc; rcases hc with rfl | hc; exact hJn; exact hne c hc
      nodup := hnd
      edges := by
        intro c hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact isChain_bridge (fun _ _ h => h.symm) hu hv hI
        · exact hc c hc'
      positive := by
        intro c hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact isChain_bridge (fun _ _ h => h.symm) hup hvp hIp
        · exact hcp c hc'
      ends := by intro c hc'; simp only [List.mem_cons] at hc'; rcases hc' with rfl | hc'; exact hJe; exact hce c hc'
      cover := by
        intro a ha
        have hh := hperm.mem_iff.mpr (P.cover a ha)
        simp only [J, List.flatten_cons, List.mem_append, List.mem_reverse] at hh ⊢
        tauto }
  refine ⟨R, ?_, rfl⟩
  have hh := hperm.length_eq
  rw [P.flat_length] at hh
  change ((x :: u).reverse ++ I ++ (y :: v) ++ C.flatten).length - Q.ncard =
    P.amount + I.length
  simp only [List.length_append, List.length_reverse] at hh ⊢
  omega

end CycleClique

end OAI
