import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawOrientations
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalRepresentative
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeExtraNeighbor

namespace OAI

/-! The extra excluded terminal vertex in terminal:weights. Orienting a
different nontrivial chain supplies it for every representative. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V}

omit [Fintype V] in
theorem exists_chain_avoiding (S : ExpandedPathSystem G Q)
    (hc : 2 ≤ S.chains.length) (x : V) : ∃ l ∈ S.chains, x ∉ l := by
  cases hcs : S.chains with
  | nil => simp only [hcs, List.length_nil] at hc; omega
  | cons l C =>
    cases C with
    | nil => simp only [hcs, List.length_cons, List.length_nil] at hc; omega
    | cons m C =>
      have hdis : l.Disjoint m :=
        (List.pairwise_cons.mp (show (l :: m :: C).Pairwise List.Disjoint by
          rw [← hcs]; exact S.disjoint)).1 m (by simp)
      by_cases hx : x ∈ l
      · exact ⟨m, by simp, fun hxm => List.disjoint_left.mp hdis hx hxm⟩
      · exact ⟨l, by simp, hx⟩

theorem IsOptimal.representative_extra_terminal {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (hc : 2 ≤ S.chains.length) {x : V} (hx : x ∈ S.representativeFinset) :
    ∃ q ∈ S.ground, q ∉ S.representativeFinset ∧
      ∀ u ∈ outsideBallFinset G S.ground x 0, ¬ G.Adj u q := by
  obtain ⟨l, hl, hxl⟩ := S.exists_chain_avoiding hc x
  have hlen := S.nontrivial l hl
  have hne : l ≠ [] := by intro he; simp [he] at hlen
  let q := l.getLast hne
  have hq : q ∈ l.getLast? := List.getLast?_eq_some_getLast hne
  have hqQ := (S.endpoints l hl).2 q hq
  have hqrep := S.terminal_not_representative hl hq
  let U := S.toRaw.completeClique.orientChains (fun r => decide (r = l))
  have hqU : q ∈ U.representatives := by
    apply RawPathSystem.representatives_orientChains_terminal S.toRaw.completeClique
      (List.mem_append_left _ hl : l ∈ S.toRaw.completeClique.chains) (by simp) hq
  have hxU : x ∈ U.representatives := by
    obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hx)
    obtain ⟨m, hm, he⟩ := List.mem_map.mp hr
    subst r
    have hxm : x ∈ m := (chainRepresentatives_sublist m).subset hxr
    have hml : m ≠ l := by intro he; subst m; exact hxl hxm
    exact RawPathSystem.representatives_orientChains_unchanged S.toRaw.completeClique
      hm (by simp [hml]) hxr
  have hUamount : U.amount = S.amount := by simp [U]
  have hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices := by
    intro v hv
    simp only [U, RawPathSystem.orientChains_vertices,
      RawPathSystem.completeClique_vertices] at hv
    exact (Finset.mem_union.mp hv).symm
  have hxq : x ≠ q := by intro he; exact hqrep (he ▸ hx)
  have hf := hopt.representatives_one_exclusion hk hQk hQ hcycle U hUamount hUvertices
    hxU hqU hxq
  refine ⟨q, Finset.mem_union_left _ hqQ, hqrep, ?_⟩
  intro u hu huq
  have hball := mem_outsideBallFinset.mp hu
  have hxu := ((outsideBall_zero (S.representativeFinset_subset_ground hx)).mp hball).1
  apply hf
  simpa only [ground, Finset.coe_union] using
    outsidePath_one_of_common_neighbor hxq hxu huq hball.1

theorem IsOptimal.terminal_first_ball {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ Q.card) (hc : 2 ≤ S.chains.length)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    {x : V} (hx : x ∈ S.representativeFinset) :
    Q.card + 1 ≤ (outsideBallFinset G S.ground x 1).card ∧
      HasIndependent (G.induce (outsideBallFinset G S.ground x 1 : Set V)) 2 := by
  obtain ⟨q, hqX, hqR, hmiss⟩ := hopt.representative_extra_terminal hk hQk hQ hcycle hc hx
  have hbig := representative_ball_one_extra hx S.representativeFinset_subset_ground
    (hopt.ground_card_le hQk) hqX hqR hexpand
    (fun y hy hne => hopt.representativeFinset_one_exclusion hk hQk hQ hcycle hx hy hne)
    hmiss
  rw [S.representativeFinset_card] at hbig
  refine ⟨by omega, independent_pair_of_not_clique ?_⟩
  intro hC
  have hh := hC.card_le_cliqueNum.trans hclique
  omega

end CycleClique.Construction.ExpandedPathSystem

namespace CycleClique.Construction
open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V}

theorem outsideBall_two_triple_of_first_pair (hCE : CEAlphaTwo) {k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hkt : 2 * t ≤ k)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ t)
    {X : Finset V} {x : V} (hXk : X.card ≤ k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hpair : HasIndependent (G.induce (outsideBallFinset G X x 1 : Set V)) 2) :
    HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 3 := by
  obtain ⟨I, hI, hind, hIcard⟩ := exists_independent_subset hpair
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  have hg := outsideBall_growth (A := ∅) (by simp) hI (by simp) (hexpand I hind hne)
  rw [hIcard] at hg
  simp only [Finset.card_empty, Nat.add_zero, Nat.reduceAdd] at hg
  apply size_test hCE hk ht hcycle hclique (outsideBallFinset G X x 2)
  exact max_lt_iff.mpr ⟨by omega, by omega⟩

end CycleClique.Construction

end OAI
