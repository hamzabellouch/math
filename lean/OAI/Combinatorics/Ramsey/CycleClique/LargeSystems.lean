import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.ChainProfiles
import OAI.Combinatorics.Ramsey.CycleClique.ChainRearrangement
import OAI.Combinatorics.Ramsey.CycleClique.CycleShortening
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorBalls
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorPaths
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.IndependenceTwo
import OAI.Combinatorics.Ramsey.CycleClique.InducedGraphs
import OAI.Combinatorics.Ramsey.CycleClique.MarkedChains
import OAI.Combinatorics.Ramsey.CycleClique.OptimalSystems
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems
import OAI.Combinatorics.Ramsey.CycleClique.SystemInsertion

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

theorem PathSystem.chains_nodup {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.chains.Nodup := by
  apply (List.nodup_flatten.mp P.nodup).2.imp_of_mem
  intro a b ha hb hd heq
  subst b
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil a (P.nonempty a ha)
  exact List.disjoint_left.mp hd hx hx

theorem PathSystem.incident_eq_edges_add_chains {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.incident = P.edgeCount + P.usedChains.length := by
  have hh := P.partition.length_eq
  simp only [List.length_append] at hh
  have hle := P.chains_length_le
  dsimp [PathSystem.incident, PathSystem.edgeCount]
  omega

theorem PathSystem.amount_pos_iff {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    0 < P.amount ↔ 0 < P.edgeCount := by
  obtain ⟨A, hA⟩ := P.exists_profile
  obtain ⟨hs, hl, hp⟩ := hA.count
  constructor
  · intro ha
    by_contra! he
    have hn : A = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hn] at hs
    omega
  · intro he
    have hh := P.edgeCount_le_amount
    omega

theorem PathSystem.rep_of_chain {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c : List V} (hc : c ∈ P.chains) {x : V}
    (hx : x ∈ markedReps Q true c) : x ∈ P.reps := by
  exact List.mem_flatten.mpr ⟨markedReps Q true c, List.mem_map.mpr ⟨c, hc, rfl⟩, hx⟩

theorem PathSystem.rep_iff_in_chain {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c : List V} (hc : c ∈ P.chains) {x : V} (hx : x ∈ c) :
    x ∈ P.reps ↔ x ∈ markedReps Q true c := by
  classical
  refine ⟨?_, P.rep_of_chain hc⟩
  intro hxr
  have hp := List.perm_cons_erase hc
  have hnd : (c ++ (P.chains.erase c).flatten).Nodup := hp.flatten.nodup_iff.mp P.nodup
  have hrp := (hp.map (markedReps Q true)).flatten
  have hv := hrp.mem_iff.mp hxr
  simp only [List.map_cons, List.flatten_cons, List.mem_append] at hv
  rcases hv with hv | hv
  · exact hv
  · exact ((List.nodup_append.mp hnd).2.2 x hx x
      ((markedReps_flatten_sublist Q _).subset hv) rfl).elim

theorem ClosedChain.rep_mem_Q_iff_head {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {c : List V} (hc : ClosedChain G Q c) {x : V} (hx : x ∈ Q) :
    x ∈ markedReps Q true c ↔ x ∈ c.head? := by
  classical
  constructor
  · intro hrep
    obtain ⟨A, B, he, hcut⟩ := (mem_markedReps Q true c x).mp hrep
    rcases hcut with ⟨rfl, _⟩ | ⟨hne, hend⟩
    · simp [he]
    · have hp := List.isChain_append.mp (he ▸ hc.positive)
      have hla : A.getLast hne ∈ A.getLast? := List.getLast?_eq_some_getLast hne
      exact ((hp.2.2 _ hla x (by simp)).elim (fun h => h (hend _ hla)) (fun h => h hx)).elim
  · intro hh
    cases c with
    | nil => simp at hh
    | cons y B =>
      have he : y = x := by simpa using hh
      subst y
      simp [markedReps]

theorem PathSystem.interior_rep_next {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {x : V} (hx : x ∈ P.reps) (hxQ : x ∉ Q) :
    ∃ c ∈ P.chains, ∃ A B : List V, ∃ y : V,
      c = A ++ x :: y :: B ∧ y ∉ P.reps := by
  obtain ⟨rc, hrc, hxc⟩ := List.mem_flatten.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrc
  obtain ⟨A, B, he, hcut⟩ := (mem_markedReps Q true c x).mp hxc
  have hnB : B ≠ [] := by
    intro hb
    have hxend : x ∈ c.getLast? := by simp [he, hb]
    exact hxQ ((P.ends c hc).2 x hxend)
  obtain ⟨y, D, hB⟩ := List.exists_cons_of_ne_nil hnB
  subst B
  refine ⟨c, hc, A, D, y, he, ?_⟩
  intro hy
  have hyc : y ∈ c := by simp [he]
  have hyrep := (P.rep_iff_in_chain hc hyc).mp hy
  have hnc := (List.nodup_flatten.mp P.nodup).1 c hc
  have hcuty := markedCut_of_split hnc hyrep (show c = (A ++ [x]) ++ y :: D by
    simpa only [List.append_assoc, List.singleton_append] using he)
  rcases hcuty with ⟨hempty, _⟩ | ⟨_, hlast⟩
  · simp at hempty
  · exact hxQ (hlast x (by simp))

theorem ClosedChain.reps_Q_count {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {c : List V} (hc : ClosedChain G Q c) (hn : c.Nodup) :
    (markedReps Q true c).countP (fun x => decide (x ∈ Q)) = 1 := by
  classical
  let x := c.head hc.nonempty
  have hxQ : x ∈ Q := hc.ends.1 x (List.head?_eq_some_head _)
  have he : ((markedReps Q true c).filter (fun x => decide (x ∈ Q))).toFinset = {x} := by
    ext y
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, hyQ⟩
      have hh := hc.rep_mem_Q_iff_head hyQ |>.mp hy
      simpa only [List.head?_eq_some_head hc.nonempty, Option.mem_def, Option.some.injEq] using hh.symm
    · rintro rfl
      exact ⟨(hc.rep_mem_Q_iff_head hxQ).mpr (List.head?_eq_some_head _), hxQ⟩
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
    (((markedReps_sublist Q true c).nodup hn).filter _), he]
  simp

theorem PathSystem.reps_Q_count {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.reps.countP (fun x => decide (x ∈ Q)) = P.chains.length := by
  classical
  simp only [PathSystem.reps, List.countP_flatten, List.map_map]
  have hm : P.chains.map (fun c => (markedReps Q true c).countP (fun x => decide (x ∈ Q))) =
      P.chains.map (fun _ => 1) := by
    apply List.map_congr_left
    intro c hc
    exact (P.closed_chain hc).reps_Q_count ((List.nodup_flatten.mp P.nodup).1 c hc)
  simp only [Function.comp_def]
  rw [hm]
  simp

theorem PathSystem.interior_reps_length {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    (P.reps.filter (fun x => x ∉ Q)).length = P.edgeCount := by
  classical
  have hh := P.reps.length_eq_countP_add_countP (fun x => decide (x ∈ Q))
  rw [P.reps_Q_count, P.reps_length] at hh
  simp only [Bool.not_eq_true, decide_eq_false_iff_not, List.countP_eq_length_filter] at hh
  dsimp [PathSystem.edgeCount]
  omega

theorem PathSystem.chains_disjoint {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c d : List V} (hc : c ∈ P.chains) (hd : d ∈ P.chains) (hne : c ≠ d) :
    c.Disjoint d := by
  classical
  have hp := List.perm_cons_erase hc
  have hnd : (c ++ (P.chains.erase c).flatten).Nodup := hp.flatten.nodup_iff.mp P.nodup
  apply List.disjoint_left.mpr
  intro x hx hy
  exact (List.nodup_append.mp hnd).2.2 x hx x
    (List.mem_flatten.mpr ⟨d, (List.mem_erase_of_ne (Ne.symm hne)).mpr hd, hy⟩) rfl

theorem markedReps_head {V : Type*} (Q : Set V) {c : List V} (hn : c ≠ []) :
    c.head hn ∈ markedReps Q true c := by
  cases c with
  | nil => contradiction
  | cons x c => simp [markedReps]

theorem PathSystem.reverse_other_rep {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c : List V} (hc : c ∈ P.chains) (hc1 : c.length ≠ 1)
    {x : V} (hx : x ∈ P.reps) (hxc : x ∉ c) :
    ∃ f : List V → Bool, ∃ y : V, y ∈ P.chains.flatten ∧ y ∉ P.reps ∧
      x ∈ (P.orient f).reps ∧ y ∈ (P.orient f).reps := by
  classical
  let f : List V → Bool := fun d => decide (d = c)
  let y := c.getLast (P.nonempty c hc)
  have hyc : y ∈ c := List.getLast_mem _
  have hyQ : y ∈ Q := (P.ends c hc).2 y (List.getLast?_eq_some_getLast _)
  have hyR : y ∉ P.reps := by
    intro hy
    have hh := (P.closed_chain hc).rep_mem_Q_iff_head hyQ |>.mp ((P.rep_iff_in_chain hc hyc).mp hy)
    have hhe : c.head (P.nonempty c hc) = c.getLast (P.nonempty c hc) := by
      simpa only [List.head?_eq_some_head (P.nonempty c hc), Option.mem_def, Option.some.injEq] using hh
    obtain ⟨z, hz⟩ := (List.Nodup.head_eq_getLast_iff (P.nonempty c hc)
      ((List.nodup_flatten.mp P.nodup).1 c hc)).mp hhe
    exact hc1 (by simp [hz])
  have hxnew : x ∈ (P.orient f).reps := by
    obtain ⟨rc, hrc, hxr⟩ := List.mem_flatten.mp hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hrc
    have hdc : d ≠ c := by
      intro he
      subst d
      exact hxc ((markedReps_sublist Q true c).subset hxr)
    have hdnew : d ∈ (P.orient f).chains := by
      rw [orient_chains]
      exact List.mem_map.mpr ⟨d, hd, by simp [f, flipChain, hdc]⟩
    exact (P.orient f).rep_of_chain hdnew hxr
  have hcnew : c.reverse ∈ (P.orient f).chains := by
    rw [orient_chains]
    exact List.mem_map.mpr ⟨c, hc, by simp [f, flipChain]⟩
  have hynew : y ∈ (P.orient f).reps := by
    apply (P.orient f).rep_of_chain hcnew
    have hh := markedReps_head Q (show c.reverse ≠ [] by simpa using P.nonempty c hc)
    simpa using hh
  exact ⟨f, y, List.mem_flatten.mpr ⟨c, hc, hyc⟩, hyR, hxnew, hynew⟩

theorem list_two_ne {α : Type*} {l : List α} (hn : l.Nodup) (hl : 2 ≤ l.length) (a : α) :
    ∃ b ∈ l, b ≠ a := by
  cases l with
  | nil => simp at hl
  | cons b l =>
    cases l with
    | nil => simp at hl
    | cons c l =>
      have hbc : b ≠ c := by
        intro he
        exact (List.nodup_cons.mp hn).1 (by simp [he])
      by_cases hba : b = a
      · exact ⟨c, by simp, by intro he; exact hbc (hba.trans he.symm)⟩
      · exact ⟨b, by simp, hba⟩

theorem PathSystem.extra_rep {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (hu : 2 ≤ P.usedChains.length) {x : V} (hx : x ∈ P.reps) :
    ∃ f : List V → Bool, ∃ y : V, y ∈ P.chains.flatten ∧ y ∉ P.reps ∧
      x ∈ (P.orient f).reps ∧ y ∈ (P.orient f).reps := by
  classical
  obtain ⟨d, hd, hxd⟩ := List.mem_flatten.mp (P.reps_sublist.subset hx)
  obtain ⟨c, hc, hcd⟩ := list_two_ne (P.chains_nodup.filter _) hu d
  have hc' : c ∈ P.chains ∧ c.length ≠ 1 := by simpa [PathSystem.usedChains] using hc
  exact P.reverse_other_rep hc'.1 hc'.2 hx (fun hxc =>
    List.disjoint_left.mp (P.chains_disjoint hc'.1 hd hcd) hxc hxd)

theorem terminal_classification_numeric {t k L e v d : ℕ}
    (ht : 9 ≤ t) (hkt : k ≤ 2*t+1) (hL : L + t = k)
    (hve : v ≤ 2*e) (hdL : d*e ≤ L) (htv : t ≤ v+d)
    (hd : 2 ≤ d) (hd6 : d ≤ 6) :
    (d = 2 ∧ t ≤ v + 2) ∨
    (d = 3 ∧ ((t = 9 ∧ e = 3 ∧ v = 6) ∨ (t = 11 ∧ e = 4 ∧ v = 8))) ∨
    (d = 5 ∧ t = 9 ∧ k = 19 ∧ e = 2 ∧ v = 4) := by
  interval_cases d
  · exact Or.inl ⟨rfl, htv⟩
  · have htt : t ≤ 11 := by nlinarith
    interval_cases t
    · exact Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, by omega, by omega⟩⟩)
    · omega
    · exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, by omega, by omega⟩⟩)
  · have htt : t ≤ 9 := by nlinarith
    omega
  · have htt : t ≤ 9 := by nlinarith
    exact Or.inr (Or.inr ⟨rfl, by omega, by omega, by omega, by omega⟩)
  · have htt : t ≤ 9 := by nlinarith
    omega

@[simp] theorem PathSystem.orient_vertices {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (f : List V → Bool) : (P.orient f).vertices = P.vertices := by
  ext x
  exact (P.orient_perm f).mem_iff

theorem PathSystem.representatives_subset {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.representatives ⊆ P.vertices := P.reps_sublist.subset

 

structure LargeSystem {V : Type*} [Fintype V] (G : SimpleGraph V) (Q : Set V)
    (k : ℕ) (P : PathSystem G Q) : Prop where
  optimal : P.Optimal k
  clique : G.IsClique Q
  no_cycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G
  nine : 9 ≤ Q.ncard
  le_k : Q.ncard ≤ k
  k_le : k ≤ 2 * Q.ncard + 1
  maximal : G.cliqueNum ≤ Q.ncard
  independent : G.indepNum ≤ k
  expansion : ∀ I : Set V, G.IsIndepSet I → I.Nonempty →
    k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard

namespace LargeSystem
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V} {k : ℕ}
  {P : PathSystem G Q} (H : LargeSystem G Q k P)
include H

 theorem degree (x : V) : k + 1 ≤ (closedNeighborhood G {x}).ncard := by
  simpa using H.expansion {x} (by simp) (Set.singleton_nonempty x)

 theorem vertices_le : P.vertices.ncard ≤ k := by
  rw [P.vertices_ncard]
  have hh := H.optimal.1
  have hk := H.le_k
  omega

 theorem orient (f : List V → Bool) : LargeSystem G Q k (P.orient f) :=
  ⟨(P.orient_optimal f).mpr H.optimal, H.clique, H.no_cycle, H.nine, H.le_k,
    H.k_le, H.maximal, H.independent, H.expansion⟩

 theorem no_one {x y : V} (hx : x ∈ P.reps) (hy : y ∈ P.reps) :
    ¬ OutsidePath G P.vertices x y 1 :=
  P.no_one_representatives H.optimal (by have := H.nine; have := H.le_k; omega)
    H.clique H.no_cycle H.le_k hx hy

 theorem misses_reps {x : V} (hx : x ∈ P.reps) :
    ∀ u ∈ outsideBall G P.vertices x 0, ∀ z ∈ P.representatives \ {x}, ¬ G.Adj u z := by
  apply outsideBall_misses_representatives P.representatives_subset hx
  intro y hy d hd hd'
  have he : d = 1 := by omega
  subst d
  exact H.no_one hx hy

 theorem extra_degree {x y : V} (hx : x ∈ P.reps) (hy : y ∈ P.vertices)
    (hyR : y ∉ P.reps)
    (hmiss : ∀ u ∈ outsideBall G P.vertices x 0, ¬ G.Adj u y) :
    Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard := by
  let Z := insert y (P.representatives \ {x})
  have ht : 1 ≤ Q.ncard := by have := H.nine; omega
  have hc : Z.ncard = Q.ncard := by
    rw [Set.ncard_insert_of_notMem (by exact fun h => hyR h.1),
      Set.ncard_sdiff_singleton_of_mem (show x ∈ P.representatives from hx), P.representatives_ncard]
    omega
  have hZ : Z ⊆ P.vertices := by
    intro z hz
    rcases hz with rfl | hz
    · exact hy
    · exact P.representatives_subset hz.1
  have hb := outsideBall_degree_bound (P.representatives_subset hx) H.vertices_le hZ H.degree
    (by
      intro u hu z hz
      rcases hz with rfl | hz
      · exact hmiss u hu
      · exact H.misses_reps hx u hu z hz)
  rw [hc] at hb
  have hs := H.vertices_le
  omega

 theorem interior_degree {x : V} (hx : x ∈ P.reps) (hxQ : x ∉ Q) :
    Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard := by
  obtain ⟨c, hc, A, B, y, he, hyR⟩ := P.interior_rep_next hx hxQ
  have hy : y ∈ P.vertices := List.mem_flatten.mpr ⟨c, hc, by simp [he]⟩
  apply H.extra_degree hx hy hyR
  apply outside_ball_misses (P.representatives_subset hx) hy
    (by intro heq; exact hyR (heq ▸ hx))
  intro d hd hd'
  have hd1 : d = 1 := by omega
  subst d
  exact P.no_one_consecutive H.optimal (by have := H.nine; have := H.le_k; omega)
    H.clique H.no_cycle H.le_k hc A B he

 theorem reverse_degree {x : V} (hx : x ∈ P.reps)
    (he : ∃ f : List V → Bool, ∃ y : V, y ∈ P.chains.flatten ∧ y ∉ P.reps ∧
      x ∈ (P.orient f).reps ∧ y ∈ (P.orient f).reps) :
    Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard := by
  obtain ⟨f, y, hy, hyR, hx', hy'⟩ := he
  apply H.extra_degree hx hy hyR
  apply outside_ball_misses (P.representatives_subset hx) hy
    (by intro heq; exact hyR (heq ▸ hx))
  intro d hd hd'
  have hd1 : d = 1 := by omega
  subst d
  simpa using (H.orient f).no_one hx' hy'

 theorem two_chains_degree (hu : 2 ≤ P.usedChains.length) {x : V} (hx : x ∈ P.reps) :
    Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard :=
  H.reverse_degree hx (P.extra_rep hu hx)

 theorem first_nonclique {x : V} (hb : Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard) :
    ¬ G.IsClique (outsideBall G P.vertices x 1) := by
  intro hc
  have hh := (clique_ncard_le_cliqueNum hc).trans H.maximal
  omega

 theorem first_pair {x : V} (hb : Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard) :
    2 ≤ independence G (outsideBall G P.vertices x 1) := by
  by_contra! hn
  exact H.first_nonclique hb (clique_of_independence_le_one (by omega))

end LargeSystem

 

theorem sum_independence_local {V : Type*} [Fintype V] {ι : Type*}
    (G : SimpleGraph V) (D : ι → Set V) (F : Finset ι)
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (D i) (D j))
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      ∀ x ∈ D i, ∀ y ∈ D j, ¬ G.Adj x y) :
    ∑ i ∈ F, independence G (D i) ≤ G.indepNum := by
  classical
  have hh : ∑ i ∈ F, independence G (D i) ≤ independence G (⋃ i ∈ F, D i) := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert i F hi ih =>
      have hu : (⋃ j ∈ insert i F, D j) = D i ∪ ⋃ j ∈ F, D j := by simp
      rw [hu, Finset.sum_insert hi]
      have hD : Disjoint (D i) (⋃ j ∈ F, D j) := by
        apply Set.disjoint_left.mpr
        intro v hvi hvF
        obtain ⟨j, hj, hvj⟩ := Set.mem_iUnion₂.mp hvF
        exact Set.disjoint_left.mp
          (hdis i (by simp) j (by simp [hj]) (by intro he; subst j; exact hi hj)) hvi hvj
      calc
        _ ≤ independence G (D i) + independence G (⋃ j ∈ F, D j) := by
          exact Nat.add_le_add_left (ih
            (fun j hj l hl hne => hdis j (by simp [hj]) l (by simp [hl]) hne)
            (fun j hj l hl hne => hsep j (by simp [hj]) l (by simp [hl]) hne)) _
        _ ≤ _ := independence_add_le Set.subset_union_left Set.subset_union_right hD (by
          intro x hx y hy
          obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
          exact hsep i (by simp) j (by simp [hj])
            (by intro he; subst j; exact hi hj) x hx y hyj)
  exact hh.trans (by simpa only [independence_univ] using
    (independence_mono (G := G) (Set.subset_univ (⋃ i ∈ F, D i))))

 theorem packing_balls {V : Type*} [Fintype V] {G : SimpleGraph V} {X : Set V}
    (F : Finset V) (r w : V → ℕ) (hF : ∀ x ∈ F, x ∈ X)
    (hno : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ∀ d, 1 ≤ d → d ≤ r x + r y + 2 →
      ¬ OutsidePath G X x y d)
    (hweight : ∀ x ∈ F, w x ≤ independence G (outsideBall G X x (r x))) :
    ∑ x ∈ F, w x ≤ G.indepNum := by
  have hh := sum_independence_local G (fun x => outsideBall G X x (r x)) F
    (fun x hx y hy hxy => (outside_balls_separated (hF x hx) (hF y hy) hxy (hno x hx y hy hxy)).1)
    (fun x hx y hy hxy => (outside_balls_separated (hF x hx) (hF y hy) hxy (hno x hx y hy hxy)).2)
  exact (Finset.sum_le_sum hweight).trans hh

abbrev PathSystem.missing {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : Set V := {x | [x] ∈ P.chains}

 theorem PathSystem.missing_eq_flat {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.missing = {x | x ∈ P.singletons.flatten} := by
  classical
  ext x
  constructor
  · intro hx
    exact List.mem_flatten.mpr ⟨[x], by simpa [PathSystem.singletons] using hx, by simp⟩
  · intro hx
    obtain ⟨c, hc, hxc⟩ := List.mem_flatten.mp hx
    have hcf : c ∈ P.chains ∧ c.length = 1 := by simpa [PathSystem.singletons] using hc
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hcf.2
    have he : x = y := by simpa using hxc
    simpa [he] using hcf.1

 theorem PathSystem.missing_subset_reps {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.missing ⊆ P.representatives := by
  intro x hx
  exact P.rep_of_chain hx (by simp [markedReps])

 theorem PathSystem.missing_subset_Q {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.missing ⊆ Q := by
  intro x hx
  exact (P.ends [x] hx).1 x (by simp)

 theorem PathSystem.missing_ncard {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.missing.ncard = P.singletons.length := by
  classical
  have he : P.missing = (↑P.singletons.flatten.toFinset : Set V) := by
    rw [P.missing_eq_flat]
    ext; simp
  rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup, P.singleton_flat_length]
  exact ((List.filter_sublist).flatten).nodup P.nodup

 theorem PathSystem.incident_add_missing {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.incident + P.missing.ncard = Q.ncard := by
  rw [P.missing_ncard]
  dsimp [PathSystem.incident]
  exact Nat.sub_add_cancel P.singletons_length_le

 theorem PathSystem.amount_pos_used {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (ha : 0 < P.amount) :
    0 < P.usedChains.length := by
  by_contra! hn
  have he : P.usedChains = [] := List.length_eq_zero_iff.mp (by omega)
  have hh := P.partition.flatten.length_eq
  simp only [he, List.nil_append, P.singleton_flat_length] at hh
  have hle := P.singletons_length_le
  have hf := P.flat_length
  omega

 theorem PathSystem.singleton_extra_rep {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (ha : 0 < P.amount)
    {x : V} (hx : x ∈ P.missing) :
    ∃ f : List V → Bool, ∃ y : V, y ∈ P.chains.flatten ∧ y ∉ P.reps ∧
      x ∈ (P.orient f).reps ∧ y ∈ (P.orient f).reps := by
  classical
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil P.usedChains
    (List.length_pos_iff.mp (P.amount_pos_used ha))
  have hcf : c ∈ P.chains ∧ c.length ≠ 1 := by simpa [PathSystem.usedChains] using hc
  apply P.reverse_other_rep hcf.1 hcf.2 (P.missing_subset_reps hx)
  intro hxc
  have hn : c ≠ [x] := by intro he; simp [he] at hcf
  exact List.disjoint_left.mp (P.chains_disjoint hcf.1 hx hn) hxc (by simp)

 theorem PathSystem.interior_representatives_ncard {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    (P.representatives \ Q).ncard = P.edgeCount := by
  classical
  have he : P.representatives \ Q =
      (↑(P.reps.filter (fun x => x ∉ Q)).toFinset : Set V) := by ext; simp
  rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup
    ((P.reps_sublist.nodup P.nodup).filter _), P.interior_reps_length]

namespace LargeSystem
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V} {k : ℕ}
  {P : PathSystem G Q} (H : LargeSystem G Q k P)
include H

 theorem two_large_first (h2t : 2 * Q.ncard ≤ k) :
    ∃ x ∈ P.reps, ∃ y ∈ P.reps, x ≠ y ∧
      Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard ∧
      Q.ncard + 1 ≤ (outsideBall G P.vertices y 1).ncard := by
  have ht := H.nine
  by_cases hs : P.vertices.ncard < k
  · have ha : ∀ x ∈ P.reps, Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard := by
      intro x hx
      have hb := outsideBall_degree_bound (P.representatives_subset hx) H.vertices_le
        (show P.representatives \ {x} ⊆ P.vertices from Set.sdiff_subset.trans P.representatives_subset)
        H.degree (H.misses_reps hx)
      rw [Set.ncard_sdiff_singleton_of_mem (show x ∈ P.representatives from hx),
        P.representatives_ncard] at hb
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard).mp (show 1 < P.representatives.ncard by
      rw [P.representatives_ncard]; omega)
    exact ⟨x, hx, y, hy, hxy, ha x hx, ha y hy⟩
  · have hs : P.vertices.ncard = k := by have := H.vertices_le; omega
    have hL : 0 < P.amount := by rw [P.vertices_ncard] at hs; omega
    by_cases he : 2 ≤ P.edgeCount
    · obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard).mp
        (show 1 < (P.representatives \ Q).ncard by rw [P.interior_representatives_ncard]; omega)
      exact ⟨x, hx.1, y, hy.1, hxy, H.interior_degree hx.1 hx.2, H.interior_degree hy.1 hy.2⟩
    · have hmiss : 2 ≤ P.missing.ncard := by
        have hv := P.incident_le_twice_edgeCount
        have hc := P.incident_add_missing
        omega
      obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard).mp (show 1 < P.missing.ncard by omega)
      exact ⟨x, P.missing_subset_reps hx, y, P.missing_subset_reps hy, hxy,
        H.reverse_degree (P.missing_subset_reps hx) (P.singleton_extra_rep hL hx),
        H.reverse_degree (P.missing_subset_reps hy) (P.singleton_extra_rep hL hy)⟩

 
 theorem short : ∃ x ∈ P.reps, ∃ y ∈ P.reps, ∃ d, 2 ≤ d ∧ d ≤ 6 ∧
    OutsidePath G P.vertices x y d := by
  classical
  by_contra hn
  have hno : ∀ x ∈ P.reps, ∀ y ∈ P.reps, ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G P.vertices x y d := by
    intro x hx y hy d hd hd' hp
    by_cases hd1 : d = 1
    · subst d; exact H.no_one hx hy hp
    · exact hn ⟨x, hx, y, hy, d, by omega, hd', hp⟩
  have hmiss : ∀ x ∈ P.reps, ∀ u ∈ outsideBall G P.vertices x 1,
      ∀ z ∈ P.representatives \ {x}, ¬ G.Adj u z := by
    intro x hx
    apply outsideBall_misses_representatives P.representatives_subset hx
    intro y hy d hd hd'
    exact hno x hx y hy d hd (by omega)
  have hpairs : ∀ x ∈ P.reps, 2 ≤ independence G (outsideBall G P.vertices x 2) := by
    intro x hx
    exact outsideBall_independent_pair P.representatives_subset hx P.representatives_ncard
      H.vertices_le H.maximal H.degree (hmiss x hx)
  let F := P.reps.toFinset
  have hFc : F.card = Q.ncard := by
    rw [List.toFinset_card_of_nodup (P.reps_sublist.nodup P.nodup), P.reps_length]
  have hpack := packing_balls F (fun _ => 2) (fun _ => 2)
    (fun x hx => P.representatives_subset (List.mem_toFinset.mp hx))
    (fun x hx y hy _ d hd hd' => hno x (List.mem_toFinset.mp hx) y
      (List.mem_toFinset.mp hy) d hd (by omega))
    (fun x hx => hpairs x (List.mem_toFinset.mp hx))
  have h2t : 2 * Q.ncard ≤ k := by
    have hi := H.independent
    simpa only [Finset.sum_const, smul_eq_mul, hFc, Nat.mul_comm] using hpack.trans hi
  obtain ⟨a, ha, b, hb, hab, haB, hbB⟩ := H.two_large_first h2t
  have htriple : ∀ x ∈ P.reps, (x = a ∨ x = b) →
      3 ≤ independence G (outsideBall G P.vertices x 2) := by
    intro x hx he
    apply outsideBall_independent_triple (by have := H.nine; omega) (by have := H.nine; omega)
      (by have := H.nine; omega) P.representatives_subset hx P.representatives_ncard
      H.vertices_le H.maximal H.no_cycle H.expansion (hmiss x hx)
    apply H.first_nonclique
    rcases he with rfl | rfl
    · exact haB
    · exact hbB
  let W : V → ℕ := fun x => 2 + if x ∈ ({a,b} : Finset V) then 1 else 0
  have hw : ∀ x ∈ F, W x ≤ independence G (outsideBall G P.vertices x 2) := by
    intro x hx
    have hxR := List.mem_toFinset.mp hx
    dsimp [W]
    split_ifs with he
    · exact htriple x hxR (by simpa using he)
    · simpa using hpairs x hxR
  have hpack' := packing_balls F (fun _ => 2) W
    (fun x hx => P.representatives_subset (List.mem_toFinset.mp hx))
    (fun x hx y hy _ d hd hd' => hno x (List.mem_toFinset.mp hx) y
      (List.mem_toFinset.mp hy) d hd (by omega)) hw
  have hsub : ({a,b} : Finset V) ⊆ F := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
  have hsum : ∑ x ∈ F, W x = 2 * Q.ncard + 2 := by
    simp only [W, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hFc,
      ← Finset.sum_filter]
    have hfilter : F.filter (fun x => x ∈ ({a,b} : Finset V)) = {a,b} := by
      ext x; simp only [Finset.mem_filter]; exact ⟨And.right, fun hx => ⟨hsub hx, hx⟩⟩
    rw [hfilter]
    simp [hab, Nat.mul_comm]
  rw [hsum] at hpack'
  have hi := hpack'.trans H.independent
  have hk := H.k_le
  omega

end LargeSystem

namespace LargeSystem
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V} {k : ℕ}
  {P : PathSystem G Q} (H : LargeSystem G Q k P)
include H

 theorem short_information {x y : V} {d : ℕ} (hx : x ∈ P.reps) (hy : y ∈ P.reps)
    (hd : 1 ≤ d) (hd6 : d ≤ 6) (hp : OutsidePath G P.vertices x y d) :
    ∃ u v : List V, ∃ D : List (List V), ∃ F : List ℕ,
      P.chains.Perm ((x :: u) :: (y :: v) :: D) ∧
      P.amount = k - Q.ncard ∧ 2 ≤ d ∧
      (D.filter (fun c => c.length = 1)).length + 2 ≤ d ∧
      AmountProfile P F ∧ ∀ a ∈ F, d ≤ a := by
  obtain ⟨I, hIl, hI, hIn, hout⟩ := hp.to_list
  have hI0 : I ≠ [] := by intro he; simp [he] at hIl; omega
  have ho : ∀ z ∈ I, z ∉ Q := fun z hz hq => hout z hz (P.cover z hq)
  simpa only [hIl] using P.short_representatives H.optimal H.clique H.no_cycle H.nine H.le_k H.k_le
    hx hy hp.2.2.1 I hI (positive_interior_chain hI0 ho) hIn
    (List.disjoint_left.mpr hout) hI0 (by omega) ho

 theorem short_heads {x y : V} {d : ℕ} (hx : x ∈ P.reps) (hy : y ∈ P.reps)
    (hd : 1 ≤ d) (hd6 : d ≤ 6) (hp : OutsidePath G P.vertices x y d) : x ∈ Q ∧ y ∈ Q := by
  obtain ⟨u, v, D, F, hP, _⟩ := H.short_information hx hy hd hd6 hp
  exact ⟨(P.ends (x :: u) (hP.mem_iff.mpr (by simp))).1 x (by simp),
    (P.ends (y :: v) (hP.mem_iff.mpr (by simp))).1 y (by simp)⟩

 theorem no_short_interior {x y : V} (hx : x ∈ P.reps) (hy : y ∈ P.reps) (hxQ : x ∉ Q)
    (d : ℕ) (hd : 1 ≤ d) (hd6 : d ≤ 6) : ¬ OutsidePath G P.vertices x y d :=
  fun hp => hxQ (H.short_heads hx hy hd hd6 hp).1

 theorem no_short_step {c : List V} (hc : c ∈ P.chains) {x y : V} (A B : List V)
    (he : c = A ++ x :: y :: B) (d : ℕ) (hd : 1 ≤ d) (hd6 : d ≤ 6) :
    ¬ OutsidePath G P.vertices x y d := by
  intro hp
  obtain ⟨I, hIl, hI, hIn, hout⟩ := hp.to_list
  have hI0 : I ≠ [] := by intro hi; simp [hi] at hIl; omega
  have ho : ∀ z ∈ I, z ∉ Q := fun z hz hq => hout z hz (P.cover z hq)
  exact P.not_short_consecutive H.optimal H.clique H.no_cycle H.nine H.le_k H.k_le hc A I B he
    hI (positive_interior_chain hI0 ho) hIn (List.disjoint_left.mpr hout) hI0 (by omega) ho

 theorem parameter {x y : V} {d : ℕ} (hx : x ∈ P.reps) (hy : y ∈ P.reps)
    (hd : 1 ≤ d) (hd6 : d ≤ 6) (hp : OutsidePath G P.vertices x y d) :
    P.amount + Q.ncard = k ∧ (∃ A, AmountProfile P A ∧ ∀ a ∈ A, d ≤ a) ∧
    ((d = 2 ∧ Q.ncard ≤ P.incident + 2 ∧ P.missing ⊆ {x,y}) ∨
     (d = 3 ∧ ((Q.ncard = 9 ∧ P.edgeCount = 3 ∧ P.incident = 6) ∨
                (Q.ncard = 11 ∧ P.edgeCount = 4 ∧ P.incident = 8)) ∧ x ∈ P.missing ∧ y ∈ P.missing) ∨
     (d = 5 ∧ Q.ncard = 9 ∧ k = 19 ∧ P.edgeCount = 2 ∧ P.incident = 4 ∧
       x ∈ P.missing ∧ y ∈ P.missing)) := by
  classical
  obtain ⟨u, v, D, F, hP, hL, hd2, hD, hF, hFd⟩ := H.short_information hx hy hd hd6 hp
  have hsk : P.amount + Q.ncard = k := by have := H.le_k; omega
  have hcount := (hP.filter (fun c => decide (c.length = 1))).length_eq
  change P.singletons.length = _ at hcount
  have huc : ((x :: u).length = 1) ↔ u = [] := by simp
  have hvc : ((y :: v).length = 1) ↔ v = [] := by simp
  simp only [List.filter_cons, huc, hvc] at hcount
  have hsingle : P.singletons.length ≤ (D.filter (fun c => c.length = 1)).length + 2 := by
    split_ifs at hcount <;> (try simp only [List.length_cons] at hcount) <;> omega
  have hvt : Q.ncard ≤ P.incident + d := by
    have hh := P.incident_add_missing
    rw [P.missing_ncard] at hh
    omega
  obtain ⟨hsum, hlen, _⟩ := hF.count
  have hm : d * P.edgeCount ≤ P.amount := by simpa [hsum, hlen] using list_sum_lower F d hFd
  have hc := terminal_classification_numeric H.nine H.k_le hsk P.incident_le_twice_edgeCount hm hvt hd2 hd6
  have hboth : P.singletons.length = d → x ∈ P.missing ∧ y ∈ P.missing := by
    intro hs
    have huv : u = [] ∧ v = [] := by
      split_ifs at hcount with hu hv <;> (try simp only [List.length_cons] at hcount) <;>
        first | exact ⟨of_decide_eq_true hu, of_decide_eq_true hv⟩ | omega
    obtain ⟨rfl, rfl⟩ := huv
    exact ⟨hP.mem_iff.mpr (by simp), hP.mem_iff.mpr (by simp)⟩
  refine ⟨hsk, ⟨F, hF, hFd⟩, ?_⟩
  rcases hc with hc | hc | hc
  · refine Or.inl ⟨hc.1, hc.2, ?_⟩
    have hDz : D.filter (fun c => decide (c.length = 1)) = [] := List.length_eq_zero_iff.mp (by omega)
    intro z hz
    have hz' := hP.mem_iff.mp hz
    simp only [List.mem_cons] at hz'
    rcases hz' with he | he | hz'
    · have hzx : z = x := List.cons.inj he |>.1
      exact Or.inl hzx
    · have hzy : z = y := List.cons.inj he |>.1
      exact Or.inr hzy
    · have hf : [z] ∈ D.filter (fun c => decide (c.length = 1)) := List.mem_filter.mpr ⟨hz', by simp⟩
      simp [hDz] at hf
  · have hs : P.singletons.length = d := by
      have hh := P.incident_add_missing
      rw [P.missing_ncard] at hh
      rcases hc.2 with h9 | h11 <;> omega
    exact Or.inr (Or.inl ⟨hc.1, hc.2, hboth hs⟩)
  · have hs : P.singletons.length = d := by
      have hh := P.incident_add_missing
      rw [P.missing_ncard] at hh
      omega
    exact Or.inr (Or.inr ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hboth hs⟩)

 theorem at_least_two_chains : 2 ≤ P.usedChains.length := by
  obtain ⟨x, hx, y, hy, d, hd, hd6, hp⟩ := H.short
  obtain ⟨hL, ⟨A, hA, hAd⟩, hh⟩ := H.parameter hx hy (by omega) hd6 hp
  obtain ⟨hs, hl, _⟩ := hA.count
  have hm := list_sum_lower A d hAd
  rw [hs, hl] at hm
  have hve := P.incident_eq_edges_add_chains
  have ht := H.nine
  have hk := H.k_le
  rcases hh with ⟨rfl, hv, _⟩ | ⟨rfl, hh, _⟩ | ⟨rfl, ht9, hk19, he, hv, _⟩
  · omega
  · rcases hh with hh | hh <;> omega
  · omega

 theorem second_triple (hk2 : 2 * Q.ncard ≤ k) {x : V} (hx : x ∈ P.reps) :
    3 ≤ independence G (outsideBall G P.vertices x 2) := by
  have hp := H.first_pair (H.two_chains_degree H.at_least_two_chains hx)
  obtain ⟨I, hIs, hI, hIc⟩ := exists_indep_of_independence G (outsideBall G P.vertices x 1)
  have hIn : I.Nonempty := (Set.ncard_pos).mp (by omega)
  have he := H.expansion I hI hIn
  have hb := outside_neighborhood_bound hIs (Set.empty_subset P.vertices) (by simp)
  simp only [Set.ncard_empty, Nat.add_zero, Nat.reduceAdd] at hb
  have hs := H.vertices_le
  have hm : 2 * k ≤ k * I.ncard := by nlinarith
  apply size_test (by have := H.nine; omega) (by have := H.nine; omega) H.no_cycle H.maximal
  omega

end LargeSystem

 theorem PathSystem.incident_representatives_ncard {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    (P.representatives \ P.missing).ncard = P.incident := by
  have hh := Set.ncard_sdiff_add_ncard_of_subset P.missing_subset_reps
  rw [P.representatives_ncard] at hh
  have hc := P.incident_add_missing
  omega

namespace LargeSystem
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V} {k : ℕ}
  {P : PathSystem G Q} (H : LargeSystem G Q k P)
include H

 theorem exclude_two_missing (hL : P.amount + Q.ncard = k)
    (hA : ∃ A, AmountProfile P A ∧ ∀ a ∈ A, 2 ≤ a)
    (hv : Q.ncard ≤ P.incident + 2) (hM : P.missing.Nonempty) : False := by
  classical
  let J := P.representatives \ P.missing
  have hJc : J.ncard = P.incident := P.incident_representatives_ncard
  have hno : ∀ x ∈ J, ∀ y ∈ J, ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G P.vertices x y d := by
    intro x hx y hy d hd hd6 hp
    obtain ⟨_, _, hc⟩ := H.parameter hx.1 hy.1 hd hd6 hp
    rcases hc with ⟨_, _, hm⟩ | ⟨_, hh, _⟩ | ⟨_, ht9, _, _, hv4, _⟩
    · obtain ⟨z, hz⟩ := hM
      rcases hm hz with he | he
      · exact hx.2 (he ▸ hz)
      · exact hy.2 (he ▸ hz)
    · rcases hh with hh | hh <;> omega
    · omega
  obtain ⟨A, hA, hAs⟩ := hA
  obtain ⟨hs, hl, _⟩ := hA.count
  have hm := list_sum_lower A 2 hAs
  rw [hs, hl] at hm
  have hve := P.incident_le_twice_edgeCount
  have hk2 : 2 * Q.ncard ≤ k + 2 := by omega
  have hweights : ∀ x ∈ J, 3 ≤ independence G (outsideBall G P.vertices x 2) := by
    intro x hx
    have hpair := H.first_pair (H.two_chains_degree H.at_least_two_chains hx.1)
    obtain ⟨I, hIs, hI, hIc⟩ := exists_indep_of_independence G (outsideBall G P.vertices x 1)
    have he := H.expansion I hI ((Set.ncard_pos).mp (by omega))
    have hmiss : ∀ u ∈ I, ∀ z ∈ J \ {x}, ¬ G.Adj u z := by
      intro u hu z hz
      apply outside_ball_misses (P.representatives_subset hx.1)
        (P.representatives_subset hz.1.1) (Ne.symm hz.2) _ u (hIs hu)
      intro d hd hd'
      exact hno x hx z hz.1 d hd (by omega)
    have hb := outside_neighborhood_bound hIs
      (show J \ {x} ⊆ P.vertices from fun z hz => P.representatives_subset hz.1.1) hmiss
    rw [Set.ncard_sdiff_singleton_of_mem hx, hJc] at hb
    norm_num only at hb
    have hr := H.vertices_le
    have he2 : 2 * k ≤ k * I.ncard := by nlinarith
    apply size_test (by have := H.nine; have := H.le_k; omega)
      (by have := H.nine; omega) H.no_cycle H.maximal
    have ht := H.nine
    change max k (2 * Q.ncard) < (outsideBall G P.vertices x 2).ncard
    omega
  have hp := packing_balls J.toFinset (fun _ => 2) (fun _ => 3)
    (fun x hx => P.representatives_subset (Set.mem_toFinset.mp hx).1)
    (fun x hx y hy _ d hd hd' => hno x (Set.mem_toFinset.mp hx) y
      (Set.mem_toFinset.mp hy) d hd (by omega))
    (fun x hx => hweights x (Set.mem_toFinset.mp hx))
  have hh : 3 * P.incident ≤ k := by
    have ha := hp.trans H.independent
    simpa only [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card', hJc, Nat.mul_comm] using ha
  have ht := H.nine
  have hk := H.k_le
  omega

 theorem exclude_three (hL : P.amount + Q.ncard = k)
    (hA : ∃ A, AmountProfile P A ∧ ∀ a ∈ A, 3 ≤ a)
    (hv : (Q.ncard = 9 ∧ P.edgeCount = 3 ∧ P.incident = 6) ∨
      (Q.ncard = 11 ∧ P.edgeCount = 4 ∧ P.incident = 8)) : False := by
  classical
  obtain ⟨A, hA, hAs⟩ := hA
  obtain ⟨hs, hl, _⟩ := hA.count
  have hm := list_sum_lower A 3 hAs
  rw [hs, hl] at hm
  have hk2 : 2 * Q.ncard ≤ k := by rcases hv with hv | hv <;> omega
  have hMc : P.missing.ncard = 3 := by have hh := P.incident_add_missing; rcases hv with hv | hv <;> omega
  obtain ⟨z, hz⟩ := (Set.ncard_pos).mp (show 0 < P.missing.ncard by omega)
  let J := insert z (P.representatives \ P.missing)
  have hJc : J.ncard = P.incident + 1 := by
    rw [Set.ncard_insert_of_notMem (by exact fun h => h.2 hz), P.incident_representatives_ncard]
  have hJR : J ⊆ P.representatives := by
    intro x hx
    rcases hx with rfl | hx
    · exact P.missing_subset_reps hz
    · exact hx.1
  have hJM : ∀ x ∈ J, x ∈ P.missing → x = z := by
    intro x hx hxM
    exact hx.elim id (fun h => (h.2 hxM).elim)
  have hno : ∀ x ∈ J, ∀ y ∈ J, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G P.vertices x y d := by
    intro x hx y hy hxy d hd hd6 hp
    obtain ⟨_, _, hc⟩ := H.parameter (hJR hx) (hJR hy) hd hd6 hp
    rcases hc with ⟨_, hv', _⟩ | ⟨_, _, hxM, hyM⟩ | ⟨_, ht9, _, _, hv4, _⟩
    · rcases hv with hv | hv <;> omega
    · exact hxy ((hJM x hx hxM).trans (hJM y hy hyM).symm)
    · rcases hv with hv | hv <;> omega
  have hp := packing_balls J.toFinset (fun _ => 2) (fun _ => 3)
    (fun x hx => P.representatives_subset (hJR (Set.mem_toFinset.mp hx)))
    (fun x hx y hy hxy d hd hd' => hno x (Set.mem_toFinset.mp hx) y
      (Set.mem_toFinset.mp hy) hxy d hd (by omega))
    (fun x hx => H.second_triple hk2 (hJR (Set.mem_toFinset.mp hx)))
  have hh : 3 * (P.incident + 1) ≤ k := by
    simpa only [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card', hJc, Nat.mul_comm]
      using hp.trans H.independent
  have hk := H.k_le
  rcases hv with hv | hv <;> omega

 theorem exclude_five (ht : Q.ncard = 9) (hk : k = 19) (hv : P.incident = 4) : False := by
  classical
  let F := P.representatives.toFinset
  let r : V → ℕ := fun x => 1 + if x ∈ P.missing then 0 else 1
  let w : V → ℕ := fun x => 2 + if x ∈ P.missing then 0 else 1
  have hF : ∀ x ∈ F, x ∈ P.reps := by
    intro x hx
    change x ∈ P.representatives
    exact Set.mem_toFinset.mp hx
  have hno : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ∀ d, 1 ≤ d → d ≤ r x + r y + 2 →
      ¬ OutsidePath G P.vertices x y d := by
    intro x hx y hy hxy d hd hd' hp
    have hd6 : d ≤ 6 := by dsimp [r] at hd'; split_ifs at hd' <;> omega
    obtain ⟨_, _, hc⟩ := H.parameter (hF x hx) (hF y hy) hd hd6 hp
    rcases hc with ⟨_, hv', _⟩ | ⟨_, hh, _⟩ | ⟨rfl, _, _, _, _, hxM, hyM⟩
    · omega
    · rcases hh with hh | hh <;> omega
    · simp only [r, ite_eq_left hxM, ite_eq_left hyM] at hd'
      omega
  have hw : ∀ x ∈ F, w x ≤ independence G (outsideBall G P.vertices x (r x)) := by
    intro x hx
    by_cases hxM : x ∈ P.missing
    · simpa only [w, r, ite_eq_left hxM, Nat.add_zero] using H.first_pair (H.two_chains_degree H.at_least_two_chains (hF x hx))
    · simpa only [w, r, ite_eq_right hxM, Nat.reduceAdd] using H.second_triple (by omega) (hF x hx)
  have hpack := packing_balls F r w (fun x hx => P.representatives_subset (hF x hx)) hno hw
  have hfilter : F.filter (fun x => x ∉ P.missing) = (P.representatives \ P.missing).toFinset := by
    ext x
    simp [F]
  have hsum : ∑ x ∈ F, w x = 22 := by
    simp only [w, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    have hi : (∑ x ∈ F, if x ∈ P.missing then 0 else 1) =
        (F.filter (fun x => x ∉ P.missing)).card := by
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp_all
    rw [hi, hfilter]
    simp only [F, ← Set.ncard_eq_toFinset_card', P.representatives_ncard,
      P.incident_representatives_ncard, ht, hv]
  rw [hsum] at hpack
  have hi := H.independent
  omega

end LargeSystem

end CycleClique

end OAI
