import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.BreadthFirst
import OAI.Combinatorics.Ramsey.CycleClique.ColouredPaths
import OAI.Combinatorics.Ramsey.CycleClique.Density
import OAI.Combinatorics.Ramsey.CycleClique.DistanceLayers
import OAI.Combinatorics.Ramsey.CycleClique.Exceptional
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.InducedGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LongPaths

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem cycle_from_dense_layer {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 8 ≤ k) {r : V} {i : ℕ} (hi : i ≤ k / 2)
    {S : Set V} (hSD : S ⊆ distanceLayer G r i) (hS : S.Nonempty)
    (hdense : MinimalDensity (G.induce S) (k / 2) (k % 2))
    (hfree : ¬ (⊤ : SimpleGraph (Fin (k / 2))) ⊑ G) :
    SimpleGraph.cycleGraph (k + 1) ⊑ G := by
  classical
  let : Nonempty S := hS.to_subtype
  let H := G.induce S
  let f : H ↪g G := SimpleGraph.Embedding.induce S
  have hfreeH : ¬ (⊤ : SimpleGraph (Fin (k / 2))) ⊑ H :=
    fun hh => hfree (hh.trans f.isContained)
  obtain ⟨hconn, hnb, horder, hdegree, hexp⟩ :=
    minimal_density_properties (by omega : 4 ≤ k / 2) (by omega : k % 2 ≤ 1) hdense hfreeH
  have horder' : k ≤ Fintype.card S := by omega
  obtain ⟨B⟩ := exists_breadthFirstParent G r
  have hneS : ∃ x ∈ S, ∃ y ∈ S, x ≠ y :=
    (Set.one_lt_ncard).mp (by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      omega)
  obtain ⟨d, hd, c, hc, x, hx, z, hz, hxz⟩ := exists_layer_split B hSD hneS
  let ℓ := k + 1 - 2 * (i - d)
  have hℓpos : 1 ≤ ℓ := by dsimp [ℓ]; omega
  have hpair : ∀ a b : S, a ≠ b → ¬ H.Adj a b →
      2 * (k / 2) ≤ (closedNeighborhood H {a, b}).ncard := by
    intro a b hab hnadj
    have hI : H.IsIndepSet {a, b} := by
      intro x hx y hy hxy hxyadj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hxy rfl
      · exact hnadj hxyadj
      · exact hnadj hxyadj.symm
      · exact hxy rfl
    have he := (hexp {a, b} hI (Set.insert_nonempty _ _)).1
    simpa only [Set.ncard_pair hab, Nat.mul_comm] using he
  have hchoose : ∃ y z : S, layerAncestor B i y.val (d + 1) ≠
      layerAncestor B i z.val (d + 1) ∧ ∃ p : H.Walk y z, p.IsPath ∧ p.length = ℓ := by
    by_cases hdepth : i - d = 1
    · obtain ⟨y, z, p, hp, hlong⟩ := long_path_min_degree
        (by omega : 2 ≤ k / 2) hconn hdegree
      have hlen : ℓ ≤ p.length := by dsimp [ℓ] at *; omega
      have htake := hp.take ℓ
      have htlen : (p.take ℓ).length = ℓ := by rw [SimpleGraph.Walk.take_length, inf_eq_left.mpr hlen]
      refine ⟨y, p.getVert ℓ, ?_, p.take ℓ, htake, htlen⟩
      have he : d + 1 = i := by omega
      simp only [he, layerAncestor_self]
      intro heq
      have hn := (htake.nil_iff_eq).mpr (Subtype.ext heq)
      have hh := hn.length_eq_zero
      omega
    · let χ : S → Fin 2 := fun v =>
        if layerAncestor B i v.val (d + 1) = layerAncestor B i x (d + 1) then 0 else 1
      have hχ : ∃ y z, χ y ≠ χ z := by
        refine ⟨⟨x, hx⟩, ⟨z, hz⟩, ?_⟩
        simp [χ, Ne.symm hxz]
      have hℓmax : ℓ ≤ 2 * (k / 2) - 2 := by dsimp [ℓ]; omega
      obtain ⟨y, z, hyz, p, hp, hlen⟩ := coloured_path H (k / 2) (by omega)
        hconn hnb hfreeH hdegree hpair χ hχ ℓ hℓpos hℓmax
      refine ⟨y, z, ?_, p, hp, hlen⟩
      intro heq
      apply hyz
      simp only [χ, heq]
  obtain ⟨y, z, hbranch, p, hp, hlen⟩ := hchoose
  have hcommon : layerAncestor B i y.val d = layerAncestor B i z.val d :=
    (hc y.val y.property).trans (hc z.val z.property).symm
  obtain ⟨q, hq, hqlen, hqint⟩ := exists_branch_path B (hSD y.property) (hSD z.property)
    hd hcommon hbranch
  let inc : H →g G := ⟨Subtype.val, fun ha => ha⟩
  let P : G.Walk y.val z.val := p.map inc
  have hP : P.IsPath := hp.map Subtype.val_injective
  have hplay : ∀ w ∈ P.support, G.dist r w = i := by
    intro w hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
    exact (hSD v.property).2
  have hcyc := cycle_of_layer_path P hP hplay q hq (by rw [hqlen]; omega) hqint
  apply (SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < k + 1)).mpr
  refine ⟨y.val, P.append q.reverse, hcyc, ?_⟩
  dsimp only [P]
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.length_map, hlen, hqlen]
  dsimp [ℓ]
  omega

 
theorem contains_half_clique {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {k : ℕ} (hk : 8 ≤ k) (hα : G.indepNum ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) :
    (⊤ : SimpleGraph (Fin (k / 2))) ⊑ G := by
  by_contra hfree
  obtain ⟨r⟩ := ‹Nonempty V›
  obtain ⟨i, _, hi, S, hSD, hS, hdense⟩ := exists_minimal_dense_layer hk hα hexp r
  exact hcycle (cycle_from_dense_layer hk hi hSD hS hdense hfree)

 

theorem triangle_free_card_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (a : ℕ) (hfree : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ G) (hα : G.indepNum ≤ a) :
    2 * Fintype.card V ≤ a * (a + 3) := by
  classical
  induction a generalizing V with
  | zero =>
    have hempty : IsEmpty V := ⟨fun v => by
      have hI : G.IsIndepSet {v} := Set.pairwise_singleton _ _
      have hc := (indep_ncard_le hI).trans hα
      simp at hc⟩
    let := hempty
    simp
  | succ a ih =>
    cases isEmpty_or_nonempty V with
    | inl he => let := he; simp
    | inr he =>
      let := he
      obtain ⟨v⟩ := he
      have hNind : G.IsIndepSet (G.neighborSet v) :=
        (SimpleGraph.isClique_compl G).mp (neighborhood_compl_clique_of_triangle_free hfree v)
      have hNcard := (indep_ncard_le hNind).trans hα
      let N := closedNeighborhood G {v}
      let R := Nᶜ
      have hNc : N.ncard ≤ a + 2 := by
        dsimp [N]
        rw [closedNeighborhood_singleton_card]
        rw [ncard_neighborSet] at hNcard
        omega
      have hαR : (G.induce R).indepNum ≤ a := by
        have hh := independence_outside_closed
          (show G.IsIndepSet {v} from Set.pairwise_singleton _ _) (Set.subset_univ {v})
        rw [independence_univ, Set.ncard_singleton, ← Set.compl_eq_univ_sdiff] at hh
        change independence G R + 1 ≤ G.indepNum at hh
        change independence G R ≤ a
        omega
      have hfreeR : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ G.induce R :=
        fun h => hfree (h.trans (SimpleGraph.Embedding.induce R).isContained)
      have hcR := ih (G.induce R) hfreeR hαR
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hcR
      have hsum := Set.ncard_add_ncard_compl N
      rw [Nat.card_eq_fintype_card] at hsum
      change 2 * R.ncard ≤ a * (a + 3) at hcR
      nlinarith

 
theorem counterexample_contains_triangle {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (_ha : 2 ≤ a) (hak : a ≤ k)
    (horder : Fintype.card V = k * a + 1) (hα : G.indepNum ≤ a) :
    (⊤ : SimpleGraph (Fin 3)) ⊑ G := by
  by_contra hfree
  have hh := triangle_free_card_bound G a hfree hα
  rw [horder] at hh
  have hcomp : a + 3 ≤ 2 * k := by omega
  have hm := Nat.mul_le_mul_left a hcomp
  nlinarith

 
theorem complete_isContained_iff_le_cliqueNum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : ℕ) :
    (⊤ : SimpleGraph (Fin t)) ⊑ G ↔ t ≤ G.cliqueNum := by
  classical
  constructor
  · intro ht
    have hn := ht.not_cliqueFree
    simp only [SimpleGraph.CliqueFree, not_forall, not_not] at hn
    obtain ⟨Q, hQ⟩ := hn
    have hh := hQ.isClique.card_le_cliqueNum
    rwa [hQ.card_eq] at hh
  · intro ht
    by_contra hn
    obtain ⟨Q, hQ⟩ := G.exists_isNClique_cliqueNum
    have hh := clique_ncard_lt hn hQ.isClique
    rw [Set.ncard_coe_finset, hQ.card_eq] at hh
    omega

 
theorem counterexample_clique_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (horder : Fintype.card V = k * a + 1) (hα : G.indepNum ≤ a)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard) :
    max 3 (k / 2) ≤ G.cliqueNum ∧ G.cliqueNum ≤ k := by
  have hthree := (complete_isContained_iff_le_cliqueNum G 3).mp
    (counterexample_contains_triangle hk ha hak horder hα)
  refine ⟨max_le hthree ?_, ?_⟩
  · by_cases hlarge : 8 ≤ k
    · let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      exact (complete_isContained_iff_le_cliqueNum G _).mp
        (contains_half_clique hlarge (hα.trans hak) hexp hcycle)
    · omega
  · by_contra hn
    have htop := (complete_isContained_iff_le_cliqueNum G (k + 1)).mpr (by omega)
    exact hcycle ((SimpleGraph.IsContained.of_le (show SimpleGraph.cycleGraph (k + 1) ≤ ⊤
      from le_top)).trans htop)

end CycleClique

end OAI
