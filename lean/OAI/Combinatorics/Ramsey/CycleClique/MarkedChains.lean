import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.OptimalSystems
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

noncomputable def markedReps {V : Type*} (Q : Set V) (b : Bool) : List V → List V
  | [] => []
  | a :: l => (if b then [a] else []) ++ markedReps Q (decide (a ∈ Q)) l

theorem markedReps_sublist {V : Type*} (Q : Set V) (b : Bool) (c : List V) :
    (markedReps Q b c).Sublist c := by
  induction c generalizing b with
  | nil => simp [markedReps]
  | cons a c ih =>
    cases b <;> simp only [markedReps, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.singleton_append]
    · exact (ih _).cons _
    · exact (ih _).cons_cons _

theorem markedReps_length {V : Type*} (Q : Set V) (b : Bool) (c : List V)
    (hne : c ≠ []) (hend : ∀ a ∈ c.getLast?, a ∈ Q) :
    (markedReps Q b c).length + 1 = c.countP (· ∈ Q) + (if b then 1 else 0) := by
  induction c generalizing b with
  | nil => contradiction
  | cons a c ih =>
    cases c with
    | nil =>
      have ha : a ∈ Q := hend a (by simp)
      cases b <;> simp [markedReps, ha]
    | cons d c =>
      have he : ∀ v ∈ (d :: c).getLast?, v ∈ Q := by simpa using hend
      have hh := ih (decide (a ∈ Q)) (by simp) he
      cases b <;> by_cases ha : a ∈ Q <;>
        simp [markedReps, ha, List.countP_cons] at hh ⊢ <;> omega

 

def MarkedCut {V : Type*} (Q : Set V) (b : Bool) (A : List V) : Prop :=
  (A = [] ∧ b = true) ∨ (A ≠ [] ∧ ∀ a ∈ A.getLast?, a ∈ Q)

theorem markedCut_cons {V : Type*} {Q : Set V} {b : Bool} {a : V} {A : List V} :
    MarkedCut Q (decide (a ∈ Q)) A ↔ MarkedCut Q b (a :: A) := by
  cases A with
  | nil => simp [MarkedCut]
  | cons d A => simp [MarkedCut]

theorem mem_markedReps {V : Type*} (Q : Set V) (b : Bool) (c : List V) (x : V) :
    x ∈ markedReps Q b c ↔ ∃ A B, c = A ++ x :: B ∧ MarkedCut Q b A := by
  induction c generalizing b with
  | nil => simp [markedReps]
  | cons a c ih =>
    simp only [markedReps, List.mem_append]
    constructor
    · rintro (h | h)
      · have hb : b = true := by cases b <;> simp_all
        have hx : x = a := by simpa [hb] using h
        subst x
        exact ⟨[], c, rfl, Or.inl ⟨rfl, hb⟩⟩
      · obtain ⟨A, B, h, hcut⟩ := (ih _).mp h
        exact ⟨a :: A, B, by simp [h], markedCut_cons.mp hcut⟩
    · rintro ⟨A, B, h, hcut⟩
      cases A with
      | nil =>
        have he : a = x ∧ c = B := by simpa using h
        have hb : b = true := by simpa [MarkedCut] using hcut
        simp [hb, he.1]
      | cons d A =>
        have he : a = d ∧ c = A ++ x :: B := by simpa using h
        rcases he with ⟨rfl, he⟩
        right
        exact (ih _).mpr ⟨A, B, he, markedCut_cons.mpr hcut⟩

noncomputable def PathSystem.reps {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : List V := (P.chains.map (markedReps Q true)).flatten

theorem markedReps_flatten_sublist {V : Type*} (Q : Set V) (C : List (List V)) :
    (C.map (markedReps Q true)).flatten.Sublist C.flatten := by
  induction C with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact (markedReps_sublist Q true c).append ih

theorem PathSystem.reps_sublist {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.reps.Sublist P.chains.flatten :=
  markedReps_flatten_sublist Q P.chains

theorem markedReps_flatten_length {V : Type*} (Q : Set V) (C : List (List V))
    (hc : ∀ c ∈ C, c ≠ [] ∧ ∀ a ∈ c.getLast?, a ∈ Q) :
    (C.map (markedReps Q true)).flatten.length = C.flatten.countP (· ∈ Q) := by
  induction C with
  | nil => simp
  | cons c cs ih =>
    have he := markedReps_length Q true c (hc c (by simp)).1 (hc c (by simp)).2
    have ht := ih (fun l hl => hc l (by simp [hl]))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.countP_append]
    simp only [↓reduceIte] at he
    omega

theorem PathSystem.reps_length {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : P.reps.length = Q.ncard :=
  (markedReps_flatten_length Q P.chains
    (fun c hc => ⟨P.nonempty c hc, (P.ends c hc).2⟩)).trans P.clique_count

theorem markedCut_of_split {V : Type*} {Q : Set V} {b : Bool} {c A B : List V} {x : V}
    (hn : c.Nodup) (hx : x ∈ markedReps Q b c) (hc : c = A ++ x :: B) :
    MarkedCut Q b A := by
  obtain ⟨A', B', hc', hcut⟩ := (mem_markedReps Q b c x).mp hx
  have hh := List.nodup_append.mp (hc ▸ hn)
  have hnA : x ∉ A := fun h => hh.2.2 x h x (by simp) rfl
  have hnB : x ∉ B := (List.nodup_cons.mp hh.2.1).1
  have he := (List.append_cons_inj_of_notMem hnA hnB).mp (hc.symm.trans hc')
  simpa only [he.1] using hcut

theorem two_mem_ordered {V : Type*} {c : List V} {x y : V}
    (hx : x ∈ c) (hy : y ∈ c) (hne : x ≠ y) :
    (∃ A u v, c = A ++ (x :: u) ++ y :: v) ∨
    (∃ A u v, c = A ++ (y :: u) ++ x :: v) := by
  obtain ⟨A, B, rfl⟩ := List.mem_iff_append.mp hx
  have hy' : y ∈ A ∨ y ∈ B := by simpa [hne.symm] using hy
  rcases hy' with h | h
  · obtain ⟨C, D, rfl⟩ := List.mem_iff_append.mp h
    exact Or.inr ⟨C, D, B, by simp only [List.append_assoc, List.cons_append]⟩
  · obtain ⟨C, D, rfl⟩ := List.mem_iff_append.mp h
    exact Or.inl ⟨A, C, D, by simp only [List.append_assoc, List.cons_append]⟩

theorem markedCuts_ordered {V : Type*} {Q : Set V} {b : Bool} {c : List V}
    {x y : V} (hn : c.Nodup) (hx : x ∈ markedReps Q b c)
    (hy : y ∈ markedReps Q b c) (A u v : List V)
    (hc : c = A ++ (x :: u) ++ y :: v) :
    MarkedCut Q b A ∧ ∀ a ∈ (x :: u).getLast?, a ∈ Q := by
  refine ⟨markedCut_of_split hn hx (by simpa only [List.append_assoc, List.cons_append] using hc), ?_⟩
  have hh := markedCut_of_split hn hy hc
  rcases hh with ⟨hh, _⟩ | ⟨_, hh⟩
  · simp at hh
  · simpa only [List.getLast?_append_of_ne_nil _ (by simp : x :: u ≠ [])] using hh

noncomputable def prefixChains {V : Type*} (A : List V) : List (List V) :=
  if A = [] then [] else [A]

@[simp] theorem prefixChains_flatten {V : Type*} (A : List V) :
    (prefixChains A).flatten = A := by
  by_cases h : A = [] <;> simp [prefixChains, h]

theorem mem_prefixChains {V : Type*} {A c : List V} :
    c ∈ prefixChains A ↔ c = A ∧ A ≠ [] := by
  by_cases h : A = [] <;> simp [prefixChains, h]

theorem prefixChains_length_le {V : Type*} (A : List V) :
    (prefixChains A).length ≤ 1 := by
  by_cases h : A = [] <;> simp [prefixChains, h]

theorem prefix_ends {V : Type*} {Q : Set V} {b : Bool} {c A B : List V}
    (hh : ∀ a ∈ c.head?, a ∈ Q) (hc : c = A ++ B) (hcut : MarkedCut Q b A)
    (hA : A ≠ []) :
    (∀ a ∈ A.head?, a ∈ Q) ∧ (∀ a ∈ A.getLast?, a ∈ Q) := by
  constructor
  · simpa only [hc, List.head?_append_of_ne_nil _ hA] using hh
  · rcases hcut with ⟨h, _⟩ | ⟨_, h⟩
    · contradiction
    · exact h

structure ClosedChain {V : Type*} (G : SimpleGraph V) (Q : Set V) (c : List V) : Prop where
  nonempty : c ≠ []
  edges : c.IsChain G.Adj
  positive : c.IsChain (fun a b => a ∉ Q ∨ b ∉ Q)
  ends : (∀ a ∈ c.head?, a ∈ Q) ∧ (∀ a ∈ c.getLast?, a ∈ Q)

structure LooseTail {V : Type*} (G : SimpleGraph V) (Q : Set V) (c : List V) : Prop where
  edges : c.IsChain G.Adj
  positive : c.IsChain (fun a b => a ∉ Q ∨ b ∉ Q)
  end_mem : ∀ a ∈ c.getLast?, a ∈ Q

theorem PathSystem.closed_chain {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c : List V} (hc : c ∈ P.chains) : ClosedChain G Q c :=
  ⟨P.nonempty c hc, P.edges c hc, P.positive c hc, P.ends c hc⟩

theorem ClosedChain.cut {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {c A : List V} {x : V} {u : List V} (hc : ClosedChain G Q c)
    (he : c = A ++ x :: u) (hcut : MarkedCut Q true A) :
    (∀ d ∈ prefixChains A, ClosedChain G Q d) ∧ LooseTail G Q (x :: u) := by
  have hed : (A ++ x :: u).IsChain G.Adj := he ▸ hc.edges
  have hpo : (A ++ x :: u).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) := he ▸ hc.positive
  constructor
  · intro d hd
    obtain ⟨rfl, hA⟩ := mem_prefixChains.mp hd
    exact ⟨hA, hed.left_of_append, hpo.left_of_append, prefix_ends hc.ends.1 he hcut hA⟩
  · refine ⟨hed.right_of_append, hpo.right_of_append, ?_⟩
    simpa only [he, List.getLast?_append_of_ne_nil _ (by simp : x :: u ≠ [])] using hc.ends.2

theorem perm_reorder_four {V : Type*} (A U B W D : List V) :
    (U ++ W ++ (A ++ B ++ D)).Perm ((A ++ U) ++ (B ++ W) ++ D) := by
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add]
  ac_rfl

theorem PathSystem.join_distinct_chains {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c d : List V} (D : List (List V)) (hP : P.chains.Perm (c :: d :: D))
    {x y : V} (A u B v I : List V) (hc : c = A ++ x :: u) (hd : d = B ++ y :: v)
    (hcutc : MarkedCut Q true A) (hcutd : MarkedCut Q true B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length := by
  have hcc := P.closed_chain (hP.mem_iff.mpr (by simp : c ∈ c :: d :: D))
  have hdd := P.closed_chain (hP.mem_iff.mpr (by simp : d ∈ c :: d :: D))
  obtain ⟨hA, hu⟩ := hcc.cut hc hcutc
  obtain ⟨hB, hv⟩ := hdd.cut hd hcutd
  let C := prefixChains A ++ prefixChains B ++ D
  have hC : ∀ l ∈ C, ClosedChain G Q l := by
    intro l hl
    simp only [C, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact hA l hl
    · exact hB l hl
    · exact P.closed_chain (hP.mem_iff.mpr (by simp [hl]))
  have hperm : ((x :: u) ++ (y :: v) ++ C.flatten).Perm P.chains.flatten := by
    apply List.Perm.trans _ hP.flatten.symm
    simp only [C, List.flatten_append, prefixChains_flatten, List.flatten_cons, hc, hd]
    simpa only [List.append_assoc] using perm_reorder_four A (x :: u) B (y :: v) D.flatten
  obtain ⟨R, hR, _⟩ := P.join_tails C u v I hperm
    (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
    (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
    hu.edges hv.edges hu.positive hv.positive hu.end_mem hv.end_mem hI hIp hIn hId
  exact ⟨R, hR⟩

theorem PathSystem.join_same_chain {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c : List V} (D : List (List V)) (hP : P.chains.Perm (c :: D))
    {x y : V} (A u v I : List V) (hc : c = A ++ (x :: u) ++ y :: v)
    (hcut : MarkedCut Q true A) (hum : ∀ a ∈ (x :: u).getLast?, a ∈ Q)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length := by
  have hcc := P.closed_chain (hP.mem_iff.mpr (by simp : c ∈ c :: D))
  obtain ⟨hA, hu⟩ := hcc.cut (by simpa only [List.append_assoc, List.cons_append] using hc) hcut
  have he : ((x :: u) ++ y :: v).IsChain G.Adj := by simpa only [List.cons_append] using hu.edges
  have hp : ((x :: u) ++ y :: v).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) := by
    simpa only [List.cons_append] using hu.positive
  have hve : ∀ a ∈ (y :: v).getLast?, a ∈ Q := by
    simpa only [hc, List.getLast?_append_of_ne_nil _ (by simp : y :: v ≠ [])] using hcc.ends.2
  let C := prefixChains A ++ D
  have hC : ∀ l ∈ C, ClosedChain G Q l := by
    intro l hl
    simp only [C, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hA l hl
    · exact P.closed_chain (hP.mem_iff.mpr (by simp [hl]))
  have hperm : ((x :: u) ++ (y :: v) ++ C.flatten).Perm P.chains.flatten := by
    apply List.Perm.trans _ hP.flatten.symm
    simp only [C, List.flatten_append, prefixChains_flatten, List.flatten_cons, hc]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  obtain ⟨R, hR, _⟩ := P.join_tails C u v I hperm
    (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
    (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
    he.left_of_append he.right_of_append hp.left_of_append hp.right_of_append
    hum hve hI hIp hIn hId
  exact ⟨R, hR⟩

theorem PathSystem.representative_replacement {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) {x y : V}
    (hx : x ∈ P.reps) (hy : y ∈ P.reps) (hxy : x ≠ y) (I : List V)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length := by
  classical
  obtain ⟨rc, hrc, hxc⟩ := List.mem_flatten.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrc
  obtain ⟨rd, hrd, hyd⟩ := List.mem_flatten.mp hy
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hrd
  have hnc := (List.nodup_flatten.mp P.nodup).1 c hc
  by_cases hcd : c = d
  · subst d
    have hp := List.perm_cons_erase hc
    rcases two_mem_ordered ((markedReps_sublist Q true c).subset hxc)
      ((markedReps_sublist Q true c).subset hyd) hxy with hh | hh
    · obtain ⟨A, u, v, he⟩ := hh
      obtain ⟨hA, hu⟩ := markedCuts_ordered hnc hxc hyd A u v he
      exact P.join_same_chain (P.chains.erase c) hp A u v I he hA hu hI hIp hIn hId
    · obtain ⟨A, u, v, he⟩ := hh
      obtain ⟨hA, hu⟩ := markedCuts_ordered hnc hyd hxc A u v he
      have hi : (y :: I.reverse ++ [x]).IsChain G.Adj := by
        simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.append_assoc, List.reverse_nil, List.nil_append, List.cons_append] using
          List.isChain_reverse.mpr (hI.imp (fun _ _ h => h.symm))
      have hip : (y :: I.reverse ++ [x]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) := by
        simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.append_assoc, List.reverse_nil, List.nil_append, List.cons_append] using
          List.isChain_reverse.mpr (hIp.imp (fun _ _ h => h.symm))
      obtain ⟨R, hR⟩ := P.join_same_chain (P.chains.erase c) hp A u v I.reverse he hA hu hi hip
        (List.nodup_reverse.mpr hIn) (by simpa using hId)
      exact ⟨R, by simpa using hR⟩
  · have hp₁ := List.perm_cons_erase hc
    have hd' : d ∈ P.chains.erase c := (List.mem_erase_of_ne (Ne.symm hcd)).mpr hd
    have hp₂ := List.perm_cons_erase hd'
    have hp := hp₁.trans (hp₂.cons c)
    obtain ⟨A, u, hec, hcutc⟩ := (mem_markedReps Q true c x).mp hxc
    obtain ⟨B, v, hed, hcutd⟩ := (mem_markedReps Q true d y).mp hyd
    exact P.join_distinct_chains ((P.chains.erase c).erase d) hp
      A u B v I hec hed hcutc hcutd hI hIp hIn hId

abbrev PathSystem.vertices {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : Set V := {v | v ∈ P.chains.flatten}

end CycleClique

end OAI
