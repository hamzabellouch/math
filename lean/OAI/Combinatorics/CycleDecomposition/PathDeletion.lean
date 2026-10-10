import OAI.Combinatorics.CycleDecomposition.Lovasz

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

structure PositiveSimplePath {V : Type cycleUniverse1} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  positive : 0 < walk.length

lemma PositiveSimplePath.endpoints_ne {V : Type cycleUniverse2} {G : SimpleGraph V}
    (P : PositiveSimplePath G) : P.start ≠ P.finish := by
  intro he
  have hz := P.isPath.nil_iff_eq.mpr he
  have := hz.length_eq_zero
  have := P.positive
  omega

theorem endpoint_path_count {V : Type cycleUniverse3} {I : Type cycleUniverse4} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hload : ∀ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) :
    Fintype.card I ≤ Fintype.card V := by
  classical
  have hsum : (∑ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card) =
      2 * Fintype.card I := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have heq : ∀ i : I,
        (∑ v : V, if (P i).start = v ∨ (P i).finish = v then 1 else 0) = 2 := by
      intro i
      have hf : (Finset.univ.filter fun v =>
          (P i).start = v ∨ (P i).finish = v) = {(P i).start, (P i).finish} := by
        ext v; simp [eq_comm]
      have hc : ({(P i).start, (P i).finish} : Finset V).card = 2 := by
        simp [(P i).endpoints_ne]
      rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have hbound := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hload v)
  rw [hsum] at hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hbound
  omega

def EndpointPathPartition {V : Type cycleUniverse5} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → PositiveSimplePath G),
    Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
    (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧
    (∀ v : V, (Finset.univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) ∧
    k ≤ Fintype.card V

def MissingEndpointTheorem : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), EndpointPathPartition G

def PathOrCycleEdgeSet {V : Type cycleUniverse6} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ 0 < p.length ∧ s = p.edgeSet) ∨
  (∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ s = p.edgeSet)

def LovaszPathCyclePartition {V : Type cycleUniverse7} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V)),
    (∀ i, PathOrCycleEdgeSet G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet ∧ 2 * k ≤ Fintype.card V

def MissingLovaszTheorem : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), LovaszPathCyclePartition G

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

def evenAugmentation {V : Type cycleUniverse8} [Fintype V] (G : SimpleGraph V) :
    SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some u, some v => G.Adj u v
    | none, some v => Even (G.degree v)
    | some u, none => Even (G.degree u)
    | none, none => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact G.adj_symm h⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact h
    · exact G.irrefl h⟩

@[simp] theorem evenAugmentation_some_adj {V : Type cycleUniverse9} [Fintype V]
    (G : SimpleGraph V) (u v : V) :
    (evenAugmentation G).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem evenAugmentation_none_adj {V : Type cycleUniverse10} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).Adj none (some v) ↔ Even (G.degree v) := Iff.rfl

@[simp] theorem evenAugmentation_some_none {V : Type cycleUniverse11} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).Adj (some v) none ↔ Even (G.degree v) := Iff.rfl

theorem evenAugmentation_degree {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).degree (some v) =
      G.degree v + if Even (G.degree v) then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  simp only [evenAugmentation_some_adj, evenAugmentation_some_none]
  have he : (∑ u : V, if G.Adj v u then 1 else 0) = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree v, G.neighborFinset_eq_filter,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  omega

theorem evenAugmentation_old_odd {V : Type cycleUniverse13} [Fintype V]
    (G : SimpleGraph V) (v : V) : Odd ((evenAugmentation G).degree (some v)) := by
  rw [evenAugmentation_degree]
  by_cases h : Even (G.degree v)
  · simp only [h, ↓reduceIte]
    rcases h with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · simpa [h] using Nat.not_even_iff_odd.mp h

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem trail_partition_degree_sum {V : Type cycleUniverse14} {I : Type cycleUniverse15} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse16} {I : Type cycleUniverse17} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

private theorem odd_load_one {V : Type cycleUniverse18} [DecidableEq V]
    (S : Finset V) (f : V → ℕ) (ho : ∀ v ∈ S, Odd (f v))
    (hs : ∑ v ∈ S, f v ≤ S.card + 1) : ∀ v ∈ S, f v = 1 := by
  intro v hv
  by_contra hn
  have hv3 : 3 ≤ f v := by rcases ho v hv with ⟨k, hk⟩; omega
  have hlow : ∑ x ∈ S, (1 + if x = v then 2 else 0) ≤ ∑ x ∈ S, f x := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases he : x = v
    · subst x; simpa using hv3
    · simp only [he, ↓reduceIte, add_zero]
      rcases ho x hx with ⟨k, hk⟩
      omega
  have heq : (∑ x ∈ S, (1 + if x = v then 2 else 0)) = S.card + 2 := by
    simp [Finset.sum_add_distrib, hv]
  omega

theorem tight_odd_trail_partition {V : Type cycleUniverse19} {I : Type cycleUniverse20} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (S : Finset V) {a b : I → V}
    (p : ∀ i, G.Walk (a i) (b i)) (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v))
    (hsize : 2 * Fintype.card I ≤ S.card + 1) :
    (∀ i, a i ≠ b i) ∧ (∀ v ∈ S,
      (Finset.univ.filter (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card = 1) := by
  classical
  let load := fun v : V => (Finset.univ.filter
    (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card
  let openParts := Finset.univ.filter (fun i => a i ≠ b i)
  have hlodd : ∀ v ∈ S, Odd (load v) := by
    intro v hv
    rw [← Nat.not_even_iff_odd, ← trail_partition_even_degree_iff G p ht hd hc v]
    exact (Nat.not_even_iff_odd.mpr (ho v hv))
  have htotal : (∑ v : V, load v) = 2 * openParts.card := by
    dsimp [load]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have he : ∀ i : I, (∑ v : V, if a i ≠ b i ∧ (v = a i ∨ v = b i) then 1 else 0) =
        if a i ≠ b i then 2 else 0 := by
      intro i
      by_cases h : a i = b i
      · simp [h]
      · have hf : (Finset.univ.filter (fun v => a i ≠ b i ∧ (v = a i ∨ v = b i))) =
            {a i, b i} := by ext v; simp [h]
        have hcard : ({a i, b i} : Finset V).card = 2 := by simp [h]
        rw [ite_eq_left h, ← hcard, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [he]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    change openParts.card * 2 = 2 * openParts.card
    omega
  have hsub : (∑ v ∈ S, load v) ≤ ∑ v : V, load v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hlow : S.card ≤ ∑ v ∈ S, load v := by
    simpa using Finset.sum_le_sum (s := S) (f := fun _ => 1) (g := load)
      (fun v hv => by rcases hlodd v hv with ⟨k, hk⟩; omega)
  have hcount : openParts.card ≤ Fintype.card I := Finset.card_le_univ _
  have hpoint := odd_load_one S load hlodd (by omega)
  refine ⟨?_, hpoint⟩
  intro i hi
  have hproper : openParts ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hh : i ∈ openParts := heq.symm ▸ Finset.mem_univ i
    simp [openParts, hi] at hh
  have hlt := Finset.card_lt_card hproper
  simp only [Finset.card_univ] at hlt
  omega

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

private theorem path_tail_delete_start {V : Type cycleUniverse21} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.tail.edgeSet = {e | e ∈ p.edgeSet ∧ a ∉ e} := by
  cases p with
  | nil => ext e; simp
  | @cons a c b h q =>
    have ha : a ∉ q.support := (List.nodup_cons.mp hp.support_nodup).1
    have hnot : ∀ e ∈ q.edgeSet, a ∉ e := by
      intro e he hae
      exact ha (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e, he, hae⟩))
    ext e
    simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.mem_edgeSet,
      SimpleGraph.Walk.edges_tail, SimpleGraph.Walk.edges_cons, List.tail_cons, List.mem_cons]
    constructor
    · intro he
      exact ⟨Or.inr he, hnot e he⟩
    · rintro ⟨he | he, hn⟩
      · subst e; exact (hn (by simp)).elim
      · exact he

private theorem path_dropLast_delete_end {V : Type cycleUniverse22} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.dropLast.edgeSet = {e | e ∈ p.edgeSet ∧ b ∉ e} := by
  have he : p.dropLast.edgeSet = p.reverse.tail.edgeSet := by
    calc
      _ = p.dropLast.reverse.edgeSet := (SimpleGraph.Walk.edgeSet_reverse _).symm
      _ = _ := by rw [SimpleGraph.Walk.reverse_dropLast, SimpleGraph.Walk.edgeSet_copy]
  rw [he, path_tail_delete_start p.reverse hp.reverse, SimpleGraph.Walk.edgeSet_reverse]

private theorem positive_avoids_of_no_incidence {V : Type cycleUniverse23} {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hpos : 0 < p.length)
    (he : ∀ e ∈ p.edgeSet, v ∉ e) : v ∉ p.support := by
  have hn : ¬p.Nil := by intro hz; have := hz.length_eq_zero; omega
  intro hv
  obtain ⟨e, he', hve⟩ := SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hn |>.mp hv
  exact he e he' hve

theorem delete_vertex_from_path {V : Type cycleUniverse24} [DecidableEq V] {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hp : p.IsPath) (hv : v ∈ p.support) :
    let q := (p.takeUntil v hv).dropLast
    let r := (p.dropUntil v hv).tail
    q.IsPath ∧ r.IsPath ∧ Disjoint q.edgeSet r.edgeSet ∧
    q.edgeSet ∪ r.edgeSet = {e | e ∈ p.edgeSet ∧ v ∉ e} ∧
    (0 < q.length → v ∉ q.support) ∧
    (0 < r.length → v ∉ r.support) ∧
    (0 < q.length → G.Adj (p.takeUntil v hv).penultimate v) ∧
    (0 < r.length → G.Adj v (p.dropUntil v hv).snd) := by
  dsimp only
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have ht : t.IsPath := hp.takeUntil hv
  have hd : d.IsPath := hp.dropUntil hv
  have heq : t.append d = p := p.take_spec hv
  have hqe : t.dropLast.edgeSet = {e | e ∈ t.edgeSet ∧ v ∉ e} :=
    path_dropLast_delete_end t ht
  have hre : d.tail.edgeSet = {e | e ∈ d.edgeSet ∧ v ∉ e} :=
    path_tail_delete_start d hd
  have hdis : Disjoint t.edgeSet d.edgeSet := by
    have hn := hp.isTrail.edges_nodup
    rw [← heq, SimpleGraph.Walk.edges_append] at hn
    have hn' := (List.nodup_append.mp hn).2.2
    apply Set.disjoint_left.mpr
    intro e het hed
    exact hn' e het e hed rfl
  refine ⟨ht.dropLast, hd.tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hqe, hre]
    exact hdis.mono (fun _ h => h.1) (fun _ h => h.1)
  · have he : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    rw [hqe, hre]
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rw [← he]
    simp only [Set.mem_union]
    tauto
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hqe ▸ he).2
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hre ▸ he).2
  · intro hpos
    apply t.adj_penultimate
    intro hn
    have hz := hn.length_eq_zero
    change 0 < t.dropLast.length at hpos
    rw [SimpleGraph.Walk.length_dropLast, hz] at hpos
    omega
  · intro hpos
    apply d.adj_snd
    intro hn
    have hz := hn.length_eq_zero
    change 0 < d.tail.length at hpos
    rw [SimpleGraph.Walk.length_tail, hz] at hpos
    omega

theorem delete_vertex_boundary_edges {V : Type cycleUniverse25} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hv : v ∈ p.support) :
    (0 < (p.takeUntil v hv).dropLast.length →
      s((p.takeUntil v hv).penultimate, v) ∈ p.edgeSet) ∧
    (0 < (p.dropUntil v hv).tail.length →
      s(v, (p.dropUntil v hv).snd) ∈ p.edgeSet) := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  constructor
  · intro hpos
    have hn : ¬ t.Nil := by
      intro hz
      change 0 < t.dropLast.length at hpos
      rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hpos
      omega
    have hm := t.mk_penultimate_end_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inl hm
  · intro hpos
    have hn : ¬ d.Nil := by
      intro hz
      change 0 < d.tail.length at hpos
      rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hpos
      omega
    have hm := d.mk_start_snd_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inr hm

theorem delete_vertex_new_ends_ne {V : Type cycleUniverse26} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hp : p.IsPath)
    (hv : v ∈ p.support)
    (hl : 0 < (p.takeUntil v hv).dropLast.length)
    (hr : 0 < (p.dropUntil v hv).tail.length) :
    (p.takeUntil v hv).penultimate ≠ (p.dropUntil v hv).snd := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  have htn : ¬t.Nil := by
    intro hz
    change 0 < t.dropLast.length at hl
    rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hl
    omega
  have hdn : ¬d.Nil := by
    intro hz
    change 0 < d.tail.length at hr
    rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hr
    omega
  have hdj := hp.isTrail.edges_nodup
  rw [← heq, SimpleGraph.Walk.edges_append] at hdj
  have hdis := (List.nodup_append.mp hdj).2.2
  intro hsame
  have ha := t.mk_penultimate_end_mem_edges htn
  have hb := d.mk_start_snd_mem_edges hdn
  apply hdis _ ha _ hb

  rw [show t.penultimate = d.snd from hsame, Sym2.eq_swap]

theorem delete_vertex_new_endpoint_load {V : Type cycleUniverse27} {I : Type cycleUniverse28} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {a b : I → V} {v : V}
    (p : ∀ i, G.Walk (a i) (b i)) (hp : ∀ i, (p i).IsPath)
    (hv : ∀ i, v ∈ (p i).support)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet) (x : V) :
    let live := fun z : I × Bool => if z.2 then
      0 < ((p z.1).takeUntil v (hv z.1)).dropLast.length else
      0 < ((p z.1).dropUntil v (hv z.1)).tail.length
    let newEnd := fun z : I × Bool => if z.2 then
      ((p z.1).takeUntil v (hv z.1)).penultimate else
      ((p z.1).dropUntil v (hv z.1)).snd
    (Finset.univ.filter fun z => live z ∧ newEnd z = x).card ≤ 1 := by
  classical
  dsimp only
  apply Finset.card_le_one.mpr
  intro z hz w hw
  obtain ⟨i, bi⟩ := z
  obtain ⟨j, bj⟩ := w
  have hi := (Finset.mem_filter.mp hz).2
  have hj := (Finset.mem_filter.mp hw).2
  have hei : s(v,x) ∈ (p i).edgeSet := by
    cases bi
    · have hx : ((p i).dropUntil v (hv i)).snd = x := hi.2
      simpa only [hx] using (delete_vertex_boundary_edges (p i) (hv i)).2 hi.1
    · have hx : ((p i).takeUntil v (hv i)).penultimate = x := hi.2
      have he := (delete_vertex_boundary_edges (p i) (hv i)).1 hi.1
      simpa only [hx, Sym2.eq_swap] using he
  have hej : s(v,x) ∈ (p j).edgeSet := by
    cases bj
    · have hx : ((p j).dropUntil v (hv j)).snd = x := hj.2
      simpa only [hx] using (delete_vertex_boundary_edges (p j) (hv j)).2 hj.1
    · have hx : ((p j).takeUntil v (hv j)).penultimate = x := hj.2
      have he := (delete_vertex_boundary_edges (p j) (hv j)).1 hj.1
      simpa only [hx, Sym2.eq_swap] using he
  have hij : i = j := by
    by_contra hn
    exact Set.disjoint_left.mp (hd hn) hei hej
  subst j
  congr 1
  cases bi <;> cases bj
  · rfl
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hj.1 hi.1
    exact (he (hj.2.trans hi.2.symm)).elim
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hi.1 hj.1
    exact (he (hi.2.trans hj.2.symm)).elim
  · rfl

structure SimplePathPiece {V : Type cycleUniverse29} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath

namespace SimplePathPiece
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype I] [DecidableEq V] {G : SimpleGraph V}

def Avoiding (p : I → SimplePathPiece G) (v : V) := {i : I // v ∉ (p i).walk.support}
def Meeting (p : I → SimplePathPiece G) (v : V) := {i : I // v ∈ (p i).walk.support}
def DeleteIndex (p : I → SimplePathPiece G) (v : V) :=
  Avoiding p v ⊕ (Meeting p v × Bool)

instance (p : I → SimplePathPiece G) (v : V) : Fintype (Avoiding p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∉ (p i).walk.support})
instance (p : I → SimplePathPiece G) (v : V) : Fintype (Meeting p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∈ (p i).walk.support})
instance (p : I → SimplePathPiece G) (v : V) : Fintype (DeleteIndex p v) :=
  inferInstanceAs (Fintype (Avoiding p v ⊕ (Meeting p v × Bool)))

def deleted (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → SimplePathPiece G
  | .inl i => p i.val
  | .inr (i,true) => ⟨_,_,((p i.val).walk.takeUntil v i.property).dropLast,
      ((p i.val).isPath.takeUntil i.property).dropLast⟩
  | .inr (i,false) => ⟨_,_,((p i.val).walk.dropUntil v i.property).tail,
      ((p i.val).isPath.dropUntil i.property).tail⟩

def parent (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → I
  | .inl i => i.val
  | .inr (i,_) => i.val

def oldEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl i => (p i.val).start = x ∨ (p i.val).finish = x
  | .inr (i,true) => (p i.val).start = x
  | .inr (i,false) => (p i.val).finish = x

def newEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl _ => False
  | .inr (i,true) => ((p i.val).walk.takeUntil v i.property).penultimate = x
  | .inr (i,false) => ((p i.val).walk.dropUntil v i.property).snd = x

lemma deleted_ends {V : Type cycleUniverse32} {I : Type cycleUniverse33} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v x : V) (j : DeleteIndex p v) :
    (deleted p v j).start = x ∨ (deleted p v j).finish = x ↔
      oldEnd p v x j ∨ newEnd p v x j := by
  rcases j with i | ⟨i,b⟩
  · simp [deleted, oldEnd, newEnd]
  · cases b <;> simp [deleted, oldEnd, newEnd, or_comm]

lemma deleted_edges_subset {V : Type cycleUniverse34} {I : Type cycleUniverse35} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v) :
    (deleted p v j).walk.edgeSet ⊆ (p (parent p v j)).walk.edgeSet := by
  rcases j with i | ⟨i,b⟩
  · exact Set.Subset.rfl
  · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
    cases b
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inr he).1
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inl he).1

lemma deleted_positive_avoids {V : Type cycleUniverse36} {I : Type cycleUniverse37} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v)
    (hpos : 0 < (deleted p v j).walk.length) : v ∉ (deleted p v j).walk.support := by
  rcases j with i | ⟨i,b⟩
  · exact i.property
  · have h := delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property
    cases b
    · exact h.2.2.2.2.2.1 hpos
    · exact h.2.2.2.2.1 hpos

lemma deleted_disjoint (p : I → SimplePathPiece G) (v : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    Pairwise fun j k => Disjoint (deleted p v j).walk.edgeSet (deleted p v k).walk.edgeSet := by
  intro j k hjk
  by_cases he : parent p v j = parent p v k
  · rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
    · exact (hjk (congrArg Sum.inl (Subtype.ext he))).elim
    · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
    · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
    · have hil : i = l := Subtype.ext he
      subst l
      cases b <;> cases c
      · exact (hjk rfl).elim
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1.symm
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1
      · exact (hjk rfl).elim
  · exact (hd he).mono (deleted_edges_subset p v j) (deleted_edges_subset p v k)

lemma deleted_old_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => oldEnd p v x j).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hjp : (p (parent p v j)).start = x ∨ (p (parent p v j)).finish = x := by
    have h := (Finset.mem_filter.mp hj).2
    rcases j with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have hkp : (p (parent p v k)).start = x ∨ (p (parent p v k)).finish = x := by
    have h := (Finset.mem_filter.mp hk).2
    rcases k with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have he := Finset.card_le_one.mp hload (parent p v j)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjp⟩) (parent p v k)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkp⟩)
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
  · exact congrArg Sum.inl (Subtype.ext he)
  · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
  · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
  · have hil : i = l := Subtype.ext he
    subst l
    cases b <;> cases c
    · rfl
    · exact (hne _ (hk'.trans hj'.symm)).elim
    · exact (hne _ (hj'.trans hk'.symm)).elim
    · rfl

lemma deleted_new_load (p : I → SimplePathPiece G) (v x : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧ newEnd p v x j).card ≤ 1 := by
  classical
  have h := delete_vertex_new_endpoint_load
    (fun i : Meeting p v => (p i.val).walk) (fun i => (p i.val).isPath)
    (fun i => i.property)
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) x
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩
  · exact False.elim hj'.2
  rcases k with l | ⟨l,c⟩
  · exact False.elim hk'.2
  apply congrArg Sum.inr
  apply Finset.card_le_one.mp h
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases b <;> exact hj'
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases c <;> exact hk'

theorem deleted_endpoint_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)).card ≤ 2 := by
  classical
  let A := Finset.univ.filter (fun j : DeleteIndex p v => oldEnd p v x j)
  let B := Finset.univ.filter (fun j : DeleteIndex p v =>
    0 < (deleted p v j).walk.length ∧ newEnd p v x j)
  have hsub : (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)) ⊆ A ∪ B := by
    intro j hj
    obtain ⟨hpos,hend⟩ := (Finset.mem_filter.mp hj).2
    rcases (deleted_ends p v x j).mp hend with ho | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpos,hn⟩)
  have ha := deleted_old_load p v x hne hload
  have hb := deleted_new_load p v x hd
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  dsimp [A,B] at hc
  omega

theorem deleted_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : DeleteIndex p v, (deleted p v j).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    refine ⟨⟨parent p v j, deleted_edges_subset p v j hj⟩,?_⟩
    rcases j with i | ⟨i,b⟩
    · intro hv
      exact i.property (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e,hj,hv⟩))
    · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
      cases b
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inr hj).2
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inl hj).2
  · rintro ⟨⟨i,hi⟩,hv⟩
    by_cases hs : v ∈ (p i).walk.support
    · have h := (delete_vertex_from_path (p i).walk (p i).isPath hs).2.2.2.1
      have he : e ∈ ((p i).walk.takeUntil v hs).dropLast.edgeSet ∪
          ((p i).walk.dropUntil v hs).tail.edgeSet := h.symm ▸ ⟨hi,hv⟩
      rcases he with hl | hr
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,true),hl⟩
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,false),hr⟩
    · exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨i,hs⟩,hi⟩

theorem deleted_positive_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length},
      (deleted p v j.val).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  rw [← deleted_union p v]
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    exact Set.mem_iUnion.mpr ⟨j.val,hj⟩
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    have hp : 0 < (deleted p v j).walk.length := by
      by_contra hn
      have hz : (deleted p v j).walk.length = 0 := by omega
      have hn' := SimpleGraph.Walk.length_eq_zero_iff.mp hz
      have he' := SimpleGraph.Walk.edges_eq_nil.mpr hn'
      have hmem : e ∈ (deleted p v j).walk.edges := hj
      exact List.not_mem_nil (he' ▸ hmem)
    exact Set.mem_iUnion.mpr ⟨⟨j,hp⟩,hj⟩

def deletedInduced (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    SimplePathPiece (G.induce {x | x ≠ v}) := by
  let q := deleted p v j.val
  have havo : ∀ x ∈ q.walk.support, x ∈ ({x | x ≠ v} : Set V) := by
    intro x hx he
    subst x
    exact deleted_positive_avoids p v j.val j.property hx
  exact ⟨_,_, q.walk.induce _ havo, by
    apply SimpleGraph.Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce _).toHom)
    simpa using q.isPath⟩

end SimplePathPiece

end
end ErdosGallai
end
end
end

end OAI
