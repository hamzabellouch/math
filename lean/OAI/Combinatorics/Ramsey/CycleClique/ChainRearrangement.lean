import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.ChainProfiles
import OAI.Combinatorics.Ramsey.CycleClique.MarkedChains
import OAI.Combinatorics.Ramsey.CycleClique.OptimalSystems
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems
import OAI.Combinatorics.Ramsey.CycleClique.SystemInsertion

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

theorem ChainAmounts.join {V : Type*} {Q : Set V} {c I : List V} {A B : List ℕ}
    {y : V} {v : List V} (hc : ChainAmounts Q c A) (hd : ChainAmounts Q (y :: v) B)
    (hI : I ≠ []) (ho : ∀ z ∈ I, z ∉ Q) :
    ChainAmounts Q (c ++ I ++ (y :: v)) (A ++ I.length :: B) := by
  induction hc with
  | singleton x hx => simpa using ChainAmounts.step x y I v B hx hI ho hd
  | step x z J D C hx hJ hJo htail ih =>
    simpa only [List.cons_append, List.append_assoc] using
      ChainAmounts.step x z J (D ++ I ++ y :: v) (C ++ I.length :: B) hx hJ hJo ih

theorem ChainAmounts.reverse {V : Type*} {Q : Set V} {c : List V} {A : List ℕ}
    (hc : ChainAmounts Q c A) : ChainAmounts Q c.reverse A.reverse := by
  induction hc with
  | singleton x hx => simpa using ChainAmounts.singleton x hx
  | step x y I B A hx hI ho htail ih =>
    have hh := ih.join (ChainAmounts.singleton x hx)
      (List.reverse_ne_nil_iff.mpr hI) (by simpa using ho)
    simpa only [List.reverse_cons, List.reverse_append, List.length_reverse,
      List.append_assoc, List.append_nil] using hh

theorem AmountProfile.of_reordered {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {C : List (List V)} {D : List (List ℕ)}
    (hp : P.chains.Perm C) (hD : List.Forall₂ (ChainAmounts Q) C D) :
    AmountProfile P D.flatten := by
  obtain ⟨E, hE, hED⟩ := List.perm_comp_forall₂ hp hD
  exact ⟨E, hE, hED.flatten⟩

theorem ChainAmounts.forall₂_exists {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (C : List (List V)) (h : ∀ c ∈ C, ClosedChain G Q c) :
    ∃ D : List (List ℕ), List.Forall₂ (ChainAmounts Q) C D := by
  induction C with
  | nil => exact ⟨[], .nil⟩
  | cons c C ih =>
    obtain ⟨A, hA⟩ := ChainAmounts.exists c (h c (by simp))
    obtain ⟨D, hD⟩ := ih (fun d hd => h d (by simp [hd]))
    exact ⟨A :: D, .cons hA hD⟩

 
theorem AmountProfile.join_starts {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P R : PathSystem G Q) {x y : V} {u v I : List V} {D : List (List V)}
    (hP : P.chains.Perm ((x :: u) :: (y :: v) :: D))
    (hR : R.chains = ((x :: u).reverse ++ I ++ (y :: v)) :: D)
    (hI : I ≠ []) (ho : ∀ z ∈ I, z ∉ Q) :
    ∃ A : List ℕ, AmountProfile P A ∧ AmountProfile R (I.length :: A) := by
  have hC : ∀ c ∈ ((x :: u) :: (y :: v) :: D), ClosedChain G Q c :=
    fun c hc => P.closed_chain (hP.mem_iff.mpr hc)
  obtain ⟨A, hA⟩ := ChainAmounts.exists (x :: u) (hC _ (by simp))
  obtain ⟨B, hB⟩ := ChainAmounts.exists (y :: v) (hC _ (by simp))
  obtain ⟨E, hE⟩ := ChainAmounts.forall₂_exists D (fun c hc => hC _ (by simp [hc]))
  have hPp := AmountProfile.of_reordered P hP (.cons hA (.cons hB hE))
  refine ⟨A ++ B ++ E.flatten, by simpa only [List.flatten_cons, List.append_assoc] using hPp, ?_⟩
  have hr : List.Forall₂ (ChainAmounts Q) R.chains ((A.reverse ++ I.length :: B) :: E) := by
    rw [hR]
    exact .cons (hA.reverse.join hB hI ho) hE
  refine ⟨(A.reverse ++ I.length :: B) :: E, hr, ?_⟩
  simp only [List.flatten_cons]
  apply List.Perm.trans ((List.reverse_perm A).append_right (I.length :: B) |>.append_right E.flatten)
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]

theorem PathSystem.join_distinct_chains_exact {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c d : List V} (D : List (List V)) (hP : P.chains.Perm (c :: d :: D))
    {x y : V} (A u B v I : List V) (hc : c = A ++ x :: u) (hd : d = B ++ y :: v)
    (hcutc : MarkedCut Q true A) (hcutd : MarkedCut Q true B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧
      R.chains = ((x :: u).reverse ++ I ++ (y :: v)) ::
      (prefixChains A ++ prefixChains B ++ D) := by
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
  obtain ⟨R, hR, hRC⟩ := P.join_tails_exact C u v I hperm
    (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
    (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
    hu.edges hv.edges hu.positive hv.positive hu.end_mem hv.end_mem hI hIp hIn hId
  exact ⟨R, hR, hRC⟩

theorem PathSystem.join_same_chain_exact {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c : List V} (D : List (List V)) (hP : P.chains.Perm (c :: D))
    {x y : V} (A u v I : List V) (hc : c = A ++ (x :: u) ++ y :: v)
    (hcut : MarkedCut Q true A) (hum : ∀ a ∈ (x :: u).getLast?, a ∈ Q)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧
      R.chains = ((x :: u).reverse ++ I ++ (y :: v)) :: (prefixChains A ++ D) := by
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
  obtain ⟨R, hR, hRC⟩ := P.join_tails_exact C u v I hperm
    (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
    (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
    he.left_of_append he.right_of_append hp.left_of_append hp.right_of_append
    hum hve hI hIp hIn hId
  exact ⟨R, hR, hRC⟩

theorem PathSystem.small_increment_run {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P R : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    {I c : List V} (hI : I ≠ []) (hI6 : I.length ≤ 6) (hout : ∀ z ∈ I, z ∉ Q)
    (hR : R.amount = P.amount + I.length) (he : R.edgeCount ≤ P.edgeCount + 1)
    (hc : c ∈ R.chains) (hin : I <:+: c) :
    P.amount = k - Q.ncard ∧ R.edgeCount = P.edgeCount + 1 ∧ 2 ≤ I.length := by
  obtain ⟨A, hA⟩ := R.exists_profile
  obtain ⟨b, hb, hbd⟩ := hA.run_bound hc hI hout hin
  have hd : 1 ≤ I.length := List.length_pos_iff.mpr hI
  obtain ⟨hL, heq, hd2, _⟩ := P.small_increment R hopt hQ hcycle ht htk hkt hd hI6 hR he hA hb hbd
  exact ⟨hL, heq, hd2⟩

theorem prefixChains_length_eq {V : Type*} (A : List V) :
    (prefixChains A).length = if A = [] then 0 else 1 := by
  by_cases h : A = [] <;> simp [prefixChains, h]

theorem PathSystem.short_distinct_chains {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    {c d : List V} (D : List (List V)) (hP : P.chains.Perm (c :: d :: D))
    {x y : V} (A u B v I : List V) (hc : c = A ++ x :: u) (hd : d = B ++ y :: v)
    (hcutc : MarkedCut Q true A) (hcutd : MarkedCut Q true B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten)
    (hI0 : I ≠ []) (hI6 : I.length ≤ 6) (hout : ∀ z ∈ I, z ∉ Q) :
    A = [] ∧ B = [] ∧ P.amount = k - Q.ncard ∧ 2 ≤ I.length ∧
      (D.filter (fun c => c.length = 1)).length + 2 ≤ I.length ∧
      ∃ F : List ℕ, AmountProfile P F ∧ ∀ a ∈ F, I.length ≤ a := by
  classical
  obtain ⟨R, hR, hRC⟩ := P.join_distinct_chains_exact D hP A u B v I hc hd hcutc hcutd
    hI hIp hIn hId
  have hPC := hP.length_eq
  simp only [List.length_cons] at hPC
  have hRCn := congrArg List.length hRC
  simp only [List.length_cons, List.length_append, prefixChains_length_eq] at hRCn
  have hPle := P.chains_length_le
  have hRle := R.chains_length_le
  have he : R.edgeCount ≤ P.edgeCount + 1 := by dsimp [PathSystem.edgeCount]; omega
  have hr := P.small_increment_run R hopt hQ hcycle ht htk hkt hI0 hI6 hout hR he
    (by rw [hRC]; simp) (show I <:+: (x :: u).reverse ++ I ++ y :: v from
      ⟨(x :: u).reverse, y :: v, rfl⟩)
  have hAB : A = [] ∧ B = [] := by
    have heq := hr.2.1
    dsimp [PathSystem.edgeCount] at heq
    split_ifs at hRCn <;> first | (constructor <;> assumption) | omega
  obtain ⟨rfl, rfl⟩ := hAB
  simp only [List.nil_append] at hc hd
  subst c d
  simp only [prefixChains, ite_true, List.nil_append] at hRC
  obtain ⟨F, hF, hRF⟩ := AmountProfile.join_starts P R hP hRC hI0 hout
  obtain ⟨hL, heq, hd2, hge⟩ := P.small_increment R hopt hQ hcycle ht htk hkt
    (List.length_pos_iff.mpr hI0) hI6 hR he hRF (by simp) (le_refl _)
  have hJlen : (((x :: u).reverse ++ I ++ y :: v)).length ≠ 1 := by simp; omega
  have hsing : R.singletons.length = (D.filter (fun c => c.length = 1)).length := by
    simp only [PathSystem.singletons, hRC, List.filter_cons, hJlen, decide_false, Bool.false_eq_true, ite_false]
  have hi : k + 1 - R.incident < R.amount := by
    by_contra! hi
    exact R.closing_interval (by omega) hQ hcycle htk (by omega) hi
  have hsle := R.singletons_length_le
  have hcount : (D.filter (fun c => c.length = 1)).length + 2 ≤ I.length := by
    dsimp [PathSystem.incident] at hi
    omega
  exact ⟨rfl, rfl, hL, hd2, hcount, F, hF, fun a ha => hge a (by simp [ha])⟩

theorem PathSystem.not_short_same_chain {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    {c : List V} (D : List (List V)) (hP : P.chains.Perm (c :: D))
    {x y : V} (A u v I : List V) (hc : c = A ++ (x :: u) ++ y :: v)
    (hcut : MarkedCut Q true A) (hum : ∀ a ∈ (x :: u).getLast?, a ∈ Q)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten)
    (hI0 : I ≠ []) (hI6 : I.length ≤ 6) (hout : ∀ z ∈ I, z ∉ Q) : False := by
  obtain ⟨R, hR, hRC⟩ := P.join_same_chain_exact D hP A u v I hc hcut hum hI hIp hIn hId
  have hPC := hP.length_eq
  simp only [List.length_cons] at hPC
  have hRCn := congrArg List.length hRC
  simp only [List.length_cons, List.length_append, prefixChains_length_eq] at hRCn
  have hPle := P.chains_length_le
  have he : R.edgeCount ≤ P.edgeCount := by dsimp [PathSystem.edgeCount]; omega
  have hr := P.small_increment_run R hopt hQ hcycle ht htk hkt hI0 hI6 hout hR (by omega)
    (by rw [hRC]; simp) (show I <:+: (x :: u).reverse ++ I ++ y :: v from
      ⟨(x :: u).reverse, y :: v, rfl⟩)
  omega

theorem PathSystem.insert_step_run {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c : List V} (hc : c ∈ P.chains) {x y : V} (A I B : List V)
    (he : c = A ++ x :: y :: B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧ R.edgeCount = P.edgeCount ∧ ∃ c ∈ R.chains, I <:+: c := by
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
  refine ⟨R, ?_, ?_, J, by simp [R], (A ++ [x]), y :: B, ?_⟩
  · have hh := hj.length_eq
    simp only [List.length_append, P.flat_length] at hh
    change (J ++ D.flatten).length - Q.ncard = P.amount + I.length
    rw [List.length_append]
    omega
  · have hh := hp.length_eq
    change Q.ncard - (J :: D).length = Q.ncard - P.chains.length
    simp only [List.length_cons] at hh ⊢
    omega
  · simp only [J, List.append_assoc, List.cons_append, List.nil_append]

theorem PathSystem.short_representatives {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    {x y : V} (hx : x ∈ P.reps) (hy : y ∈ P.reps) (hxy : x ≠ y) (I : List V)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten)
    (hI0 : I ≠ []) (hI6 : I.length ≤ 6) (hout : ∀ z ∈ I, z ∉ Q) :
    ∃ u v : List V, ∃ D : List (List V), ∃ F : List ℕ,
      P.chains.Perm ((x :: u) :: (y :: v) :: D) ∧
      P.amount = k - Q.ncard ∧ 2 ≤ I.length ∧
      (D.filter (fun c => c.length = 1)).length + 2 ≤ I.length ∧
      AmountProfile P F ∧ ∀ a ∈ F, I.length ≤ a := by
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
      exact (P.not_short_same_chain hopt hQ hcycle ht htk hkt
        (P.chains.erase c) hp A u v I he hA hu hI hIp hIn hId hI0 hI6 hout).elim
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
      exact (P.not_short_same_chain hopt hQ hcycle ht htk hkt
        (P.chains.erase c) hp A u v I.reverse he hA hu hi hip (by simpa using hIn)
        (by simpa using hId) (by simpa using hI0) (by simpa using hI6) (by simpa using hout)).elim
  · have hp₁ := List.perm_cons_erase hc
    have hd' : d ∈ P.chains.erase c := (List.mem_erase_of_ne (Ne.symm hcd)).mpr hd
    have hp₂ := List.perm_cons_erase hd'
    have hp := hp₁.trans (hp₂.cons c)
    obtain ⟨A, u, hec, hcutc⟩ := (mem_markedReps Q true c x).mp hxc
    obtain ⟨B, v, hed, hcutd⟩ := (mem_markedReps Q true d y).mp hyd
    obtain ⟨rfl, rfl, hL, hd2, hS, F, hF, hFa⟩ :=
      P.short_distinct_chains hopt hQ hcycle ht htk hkt ((P.chains.erase c).erase d)
        hp A u B v I hec hed hcutc hcutd hI hIp hIn hId hI0 hI6 hout
    simp only [List.nil_append] at hec hed
    exact ⟨u, v, (P.chains.erase c).erase d, F, by simpa [← hec, ← hed] using hp,
      hL, hd2, hS, hF, hFa⟩

theorem PathSystem.not_short_consecutive {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    {c : List V} (hc : c ∈ P.chains) {x y : V} (A I B : List V)
    (he : c = A ++ x :: y :: B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten)
    (hI0 : I ≠ []) (hI6 : I.length ≤ 6) (hout : ∀ z ∈ I, z ∉ Q) : False := by
  obtain ⟨R, hR, heR, cR, hcR, hiR⟩ := P.insert_step_run hc A I B he hI hIp hIn hId
  have hh := P.small_increment_run R hopt hQ hcycle ht htk hkt hI0 hI6 hout hR (by omega) hcR hiR
  omega

noncomputable def flipChain {V : Type*} (b : Bool) (c : List V) : List V :=
  if b then c.reverse else c

@[simp] theorem flipChain_length {V : Type*} (b : Bool) (c : List V) :
    (flipChain b c).length = c.length := by cases b <;> simp [flipChain]

theorem flipChain_perm {V : Type*} (b : Bool) (c : List V) :
    (flipChain b c).Perm c := by cases b <;> simp [flipChain]

theorem flipChains_flatten_perm {V : Type*} (f : List V → Bool) (C : List (List V)) :
    (C.map (fun c => flipChain (f c) c)).flatten.Perm C.flatten := by
  induction C with
  | nil => simp
  | cons c C ih => exact (flipChain_perm (f c) c).append ih

noncomputable def PathSystem.orient {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (f : List V → Bool) : PathSystem G Q := by
  classical
  let C := P.chains.map (fun c => flipChain (f c) c)
  have hp : C.flatten.Perm P.chains.flatten := flipChains_flatten_perm f P.chains
  refine {
    chains := C
    nonempty := ?_
    nodup := hp.nodup_iff.mpr P.nodup
    edges := ?_
    positive := ?_
    ends := ?_
    cover := fun v hv => hp.mem_iff.mpr (P.cover v hv) }
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have hn := P.nonempty d hd
    cases hf : f d <;> simpa [flipChain, hf] using hn
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have he := P.edges d hd
    cases hf : f d
    · simpa [flipChain, hf] using he
    · simpa [flipChain, hf] using List.isChain_reverse.mpr (he.imp (fun _ _ h => h.symm))
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have he := P.positive d hd
    cases hf : f d
    · simpa [flipChain, hf] using he
    · simpa [flipChain, hf] using List.isChain_reverse.mpr (he.imp (fun _ _ h => h.symm))
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have he := P.ends d hd
    cases hf : f d
    · simpa [flipChain, hf] using he
    · simpa [flipChain, hf] using And.intro he.2 he.1

@[simp] theorem PathSystem.orient_chains {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).chains = P.chains.map (fun c => flipChain (f c) c) := rfl

theorem PathSystem.orient_perm {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).chains.flatten.Perm P.chains.flatten := flipChains_flatten_perm f P.chains

@[simp] theorem PathSystem.orient_amount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).amount = P.amount := by
  change (P.orient f).chains.flatten.length - Q.ncard = P.chains.flatten.length - Q.ncard
  rw [(P.orient_perm f).length_eq]

@[simp] theorem PathSystem.orient_edgeCount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).edgeCount = P.edgeCount := by simp [PathSystem.edgeCount]

@[simp] theorem PathSystem.orient_singletons_length {V : Type*}
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).singletons.length = P.singletons.length := by
  classical
  simp only [PathSystem.singletons, orient_chains, List.filter_map, List.length_map]
  congr 2
  funext c
  simp only [Function.comp_apply, flipChain_length]

@[simp] theorem PathSystem.orient_incident {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).incident = P.incident := by simp [PathSystem.incident]

@[simp] theorem PathSystem.orient_optimal {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (f : List V → Bool) {k : ℕ} :
    (P.orient f).Optimal k ↔ P.Optimal k := by simp [PathSystem.Optimal]

end CycleClique

end OAI
