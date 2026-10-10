import OAI.Combinatorics.CycleDecomposition.ReservoirCycles

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma walks_edges_disjoint_of_support {V : Type cycleUniverse1} {G H : SimpleGraph V}
    {x y a b : V} (p : G.Walk x y) (q : H.Walk a b)
    (h : p.support.Disjoint q.support) : Disjoint p.edgeSet q.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he he'
  induction e using Sym2.ind with
  | _ u v =>
    exact h (p.fst_mem_support_of_mem_edges he) (q.fst_mem_support_of_mem_edges he')

lemma walk_edges_disjoint_spokes_of_outside {V : Type cycleUniverse2} {I : Type cycleUniverse3} {G : SimpleGraph V}
    {u v : V} (Q : G.Walk u v) (W : Set V) (x y a b : I → V)
    (hQ : ∀ z ∈ Q.support, z ∉ W) (ha : ∀ i, a i ∈ W) (hb : ∀ i, b i ∈ W) :
    ∀ i, Disjoint Q.edgeSet ({s(x i,a i), s(y i,b i)} : Set (Sym2 V)) := by
  intro i
  apply Set.disjoint_left.mpr
  intro e he he'
  rcases he' with rfl | he'
  · exact hQ _ (Q.snd_mem_support_of_mem_edges he) (ha i)
  · have heq : e = s(y i,b i) := he'
    subst e
    exact hQ _ (Q.snd_mem_support_of_mem_edges he) (hb i)

lemma walk_edges_disjoint_spokes_of_inside {V : Type cycleUniverse4} {I : Type cycleUniverse5} {G : SimpleGraph V}
    {u v : V} (Q : G.Walk u v) (W : Set V) (x y a b : I → V)
    (hQ : ∀ z ∈ Q.support, z ∈ W) (hx : ∀ i, x i ∉ W) (hy : ∀ i, y i ∉ W) :
    ∀ i, Disjoint Q.edgeSet ({s(x i,a i), s(y i,b i)} : Set (Sym2 V)) := by
  intro i
  apply Set.disjoint_left.mpr
  intro e he he'
  rcases he' with rfl | he'
  · exact hx i (hQ _ (Q.fst_mem_support_of_mem_edges he))
  · have heq : e = s(y i,b i) := he'
    subst e
    exact hy i (hQ _ (Q.fst_mem_support_of_mem_edges he))

theorem uniform_reservoir_completion (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V) (Q : ∀ i, G.Walk (x i) (y i)),
      (∀ i, (Q i).IsPath) → (∀ i, 0 < (Q i).length) →
      (∀ i v, v ∈ (Q i).support → v ∉ W) →
      Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet) →
      (∀ v, endpointLoad univ x y v ≤ 2) →
      ∀ r : V × Fin 2 → V,
      (∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t))) →
      (∀ v, v ∉ W → r (v,0) ≠ r (v,1)) →
      (∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ (a b : I → V) (q : ∀ i, G.Walk (a i) (b i))
        (C : ∀ i, G.Walk (x i) (x i)),
        (∀ i, (C i).IsCycle) ∧
        Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
        (∀ i, (C i).edgeSet = (Q i).edgeSet ∪ (q i).edgeSet ∪
          {s(x i,a i),s(y i,b i)}) ∧
        (∀ i, (q i).edgeSet ⊆ P.edgeSet ∧ ∀ v ∈ (q i).support, v ∈ W) ∧
        Function.Injective (fun z : I × Fin 2 =>
          if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
        (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) := by
  obtain ⟨D₀,hD₀,hrouting⟩ := uniform_assigned_reservoir_routing c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y Q hQ hpos hout hQQ hl r hrep hrepne hcap
  have hne : ∀ i, x i ≠ y i := by
    intro i hi
    have hz := ((hQ i).nil_iff_eq.mpr hi).length_eq_zero
    have := hpos i
    omega
  have hx : ∀ i, x i ∉ W := fun i => hout i _ (Q i).start_mem_support
  have hy : ∀ i, y i ∉ W := fun i => hout i _ (Q i).end_mem_support
  obtain ⟨a,b,q,hab,hsp,hq,hdd,ha',hb',hPedge⟩ :=
    hrouting D hD V G P hPG W hexp hW hr I x y hne hx hy hl r hrep hrepne hcap
  have ha : ∀ i, a i ∈ W := fun i => (hq i).2.2 _ (q i).start_mem_support
  have hb : ∀ i, b i ∈ W := fun i => (hq i).2.2 _ (q i).end_mem_support
  have hdisj : ∀ i j, (Q i).support.Disjoint (q j).support := by
    intro i j
    exact List.disjoint_left.mpr (fun v hv hv' => hout i v hv ((hq j).2.2 v hv'))
  let C := fun i => (Q i).append (reservoirReturn (q i) (hab i).1 (hab i).2)
  have hfamily := reservoir_cycle_family Q q (fun i => (hab i).1) (fun i => (hab i).2)
    hQ hpos (fun i => (hq i).1) (fun i => hdisj i i) hQQ hdd hsp
    (fun i j => walks_edges_disjoint_of_support _ _ (hdisj i j))
    (fun i => walk_edges_disjoint_spokes_of_outside (Q i) W x y a b (hout i) ha hb)
    (fun i => walk_edges_disjoint_spokes_of_inside (q i) W x y a b (hq i).2.2 hx hy)
  refine ⟨a,b,q,C,hfamily.1,hfamily.2.1,?_,?_,hsp,ha',hb'⟩
  · intro i
    exact (reservoir_path_closure (Q i) (q i) (hQ i) (hpos i) (hq i).1
      (hdisj i i) (hab i).1 (hab i).2).2.1
  · intro i
    exact ⟨hPedge i,(hq i).2.2⟩

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph
attribute [local instance] Classical.propDecidable

lemma exists_reservoir_avoided {V : Type cycleUniverse6} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (x y : V) :
    ∃ i, x ∉ W i ∧ y ∉ W i := by
  by_contra hno
  have h : ∀ i, x ∈ W i ∨ y ∈ W i := by
    intro i
    by_contra! hi
    exact hno ⟨i,hi⟩
  have h01 := Set.disjoint_left.mp (hW (show (0 : Fin 3) ≠ 1 by decide))
  have h02 := Set.disjoint_left.mp (hW (show (0 : Fin 3) ≠ 2 by decide))
  have h12 := Set.disjoint_left.mp (hW (show (1 : Fin 3) ≠ 2 by decide))
  rcases h 0 with hx0 | hy0 <;>
    rcases h 1 with hx1 | hy1 <;>
    rcases h 2 with hx2 | hy2
  all_goals first
    | exact h01 hx0 hx1
    | exact h02 hx0 hx2
    | exact h12 hx1 hx2
    | exact h01 hy0 hy1
    | exact h02 hy0 hy2
    | exact h12 hy1 hy2

lemma exists_edge_reservoir_avoided {V : Type cycleUniverse7} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) :
    ∃ i, ∀ v ∈ e, v ∉ W i := by
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨i,hx,hy⟩ := exists_reservoir_avoided W hW x y
    refine ⟨i,?_⟩
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hx
    · exact hy

noncomputable def reservoirColor {V : Type cycleUniverse8} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) : Fin 3 :=
  (exists_edge_reservoir_avoided W hW e).choose

lemma reservoirColor_avoids {V : Type cycleUniverse9} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) :
    ∀ v ∈ e, v ∉ W (reservoirColor W hW e) :=
  (exists_edge_reservoir_avoided W hW e).choose_spec

def complementaryReservoirGraph {V : Type cycleUniverse10} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ reservoirColor W hW s(x,y) = i
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact G.loopless.irrefl x h.1⟩

lemma complementaryReservoirGraph_edges {V : Type cycleUniverse11} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) :
    (complementaryReservoirGraph G W hW i).edgeSet =
      {e | e ∈ G.edgeSet ∧ reservoirColor W hW e = i} := by
  ext e
  induction e using Sym2.ind with
  | _ x y => rfl

theorem complementary_reservoir_graphs {V : Type cycleUniverse12} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j)) :
    (∀ i, complementaryReservoirGraph G W hW i ≤ G) ∧
    (∀ i x y, (complementaryReservoirGraph G W hW i).Adj x y →
      x ∉ W i ∧ y ∉ W i) ∧
    Pairwise (fun i j => Disjoint (complementaryReservoirGraph G W hW i).edgeSet
      (complementaryReservoirGraph G W hW j).edgeSet) ∧
    (⋃ i, (complementaryReservoirGraph G W hW i).edgeSet) = G.edgeSet := by
  refine ⟨fun _ _ _ h => h.1, ?_, ?_, ?_⟩
  · intro i x y h
    have hx := reservoirColor_avoids W hW s(x,y) x (Sym2.mem_mk_left x y)
    have hy := reservoirColor_avoids W hW s(x,y) y (Sym2.mem_mk_right x y)
    rw [h.2] at hx hy
    exact ⟨hx,hy⟩
  · intro i j hij
    rw [complementaryReservoirGraph_edges, complementaryReservoirGraph_edges]
    exact Set.disjoint_left.mpr fun _ he hj => hij (he.2.symm.trans hj.2)
  · ext e
    simp only [Set.mem_iUnion, complementaryReservoirGraph_edges, Set.mem_ofPred]
    constructor
    · rintro ⟨i,he,_⟩; exact he
    · intro he; exact ⟨reservoirColor W hW e, he, rfl⟩

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

def reservoirInternal {V : Type cycleUniverse13} (P : SimpleGraph V) (W : Set V) : Set (Sym2 V) :=
  {e | e ∈ P.edgeSet ∧ ∀ v ∈ e, v ∈ W}

noncomputable def reservoirSpokes {V : Type cycleUniverse14} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) : Finset (Sym2 V) :=
  (Wᶜ ×ˢ univ).image (fun z => s(z.1,r z))

lemma mem_reservoirSpokes {V : Type cycleUniverse15} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) (e : Sym2 V) :
    e ∈ reservoirSpokes W r ↔ ∃ v ∉ W, ∃ t : Fin 2, e = s(v,r (v,t)) := by
  simp only [reservoirSpokes, Finset.mem_image, Finset.mem_product,
    Finset.mem_compl, Finset.mem_univ, and_true, Prod.exists]
  constructor
  · rintro ⟨v,t,hv,he⟩
    exact ⟨v,hv,t,he.symm⟩
  · rintro ⟨v,hv,t,he⟩
    exact ⟨v,t,hv,he.symm⟩

lemma reservoirSpokes_card_le {V : Type cycleUniverse16} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) :
    (reservoirSpokes W r).card ≤ 2 * Fintype.card V := by
  apply (Finset.card_image_le).trans
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have := Finset.card_le_univ Wᶜ
  omega

lemma reservoirSpokes_subset {V : Type cycleUniverse17} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (W : Finset V) (r : V × Fin 2 → V)
    (hr : ∀ v, v ∉ W → ∀ t, P.Adj v (r (v,t))) :
    (reservoirSpokes W r : Set (Sym2 V)) ⊆ P.edgeSet := by
  intro e he
  obtain ⟨v,hv,t,rfl⟩ := (mem_reservoirSpokes W r e).mp he
  exact hr v hv t

lemma reservoirInternal_spokes_disjoint {V : Type cycleUniverse18} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (W : Finset V) (r : V × Fin 2 → V) :
    Disjoint (reservoirInternal P W) (reservoirSpokes W r : Set (Sym2 V)) := by
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨v,hv,t,rfl⟩ := (mem_reservoirSpokes W r e).mp he'
  exact hv (he.2 _ (Sym2.mem_mk_left _ _))

theorem reservoir_reservations {V : Type cycleUniverse19} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Fin 3 → SimpleGraph V) (W : Fin 3 → Finset V)
    (r : Fin 3 → V × Fin 2 → V)
    (hPG : ∀ i, P i ≤ G)
    (hPP : Pairwise fun i j => Disjoint (P i).edgeSet (P j).edgeSet)
    (hr : ∀ i v, v ∉ W i → ∀ t, (P i).Adj v (r i (v,t))) :
    let R := fun i => reservoirInternal (P i) (W i)
    let O := fun i => (reservoirSpokes (W i) (r i) : Set (Sym2 V))
    (∀ i, R i ⊆ G.edgeSet ∧ O i ⊆ G.edgeSet) ∧
    Pairwise (fun i j => Disjoint (R i ∪ O i) (R j ∪ O j)) ∧
    (∀ i, Disjoint (R i) (O i)) ∧
    Disjoint (⋃ i, R i) (⋃ i, O i) ∧
    (∑ i, (reservoirSpokes (W i) (r i)).card) ≤ 6 * Fintype.card V := by
  dsimp only
  have hR : ∀ i, reservoirInternal (P i) (W i) ⊆ (P i).edgeSet := fun _ _ he => he.1
  have hO := fun i => reservoirSpokes_subset (P i) (W i) (r i) (hr i)
  have hU : ∀ i, reservoirInternal (P i) (W i) ∪
      (reservoirSpokes (W i) (r i) : Set (Sym2 V)) ⊆ (P i).edgeSet :=
    fun i => Set.union_subset (hR i) (hO i)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨(hR i).trans (SimpleGraph.edgeSet_mono (hPG i)),
      (hO i).trans (SimpleGraph.edgeSet_mono (hPG i))⟩
  · intro i j hij
    exact (hPP hij).mono (hU i) (hU j)
  · exact fun i => reservoirInternal_spokes_disjoint (P i) (W i) (r i)
  · rw [Set.disjoint_iUnion_left]
    intro i
    rw [Set.disjoint_iUnion_right]
    intro j
    by_cases hij : i = j
    · subst j
      exact reservoirInternal_spokes_disjoint (P i) (W i) (r i)
    · exact (hPP hij).mono (hR i) (hO j)
  · calc
      _ ≤ ∑ _i : Fin 3, 2 * Fintype.card V :=
        Finset.sum_le_sum (fun i _ => reservoirSpokes_card_le (W i) (r i))
      _ = _ := by simp; omega

lemma complementary_walk_outside {V : Type cycleUniverse20} {G : SimpleGraph V}
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) {x y : V} (q : (complementaryReservoirGraph G W hW i).Walk x y)
    (hq : 0 < q.length) : ∀ v ∈ q.support, v ∉ W i := by
  have hn : ¬ q.Nil := by
    intro h
    have hz := h.length_eq_zero
    omega
  intro v hv
  obtain ⟨e,he,hve⟩ := SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hn |>.mp hv
  have heG := q.edges_subset_edgeSet he
  have hecol : reservoirColor W hW e = i := by
    rw [complementaryReservoirGraph_edges] at heG
    exact heG.2
  exact hecol ▸ reservoirColor_avoids W hW e v hve

theorem complementary_reservation_ledger {V : Type cycleUniverse21} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (E : Set (Sym2 V)) (hE : E ⊆ G.edgeSet) :
    let H := G.deleteEdges E
    let K := fun i => complementaryReservoirGraph H W hW i
    Pairwise (fun i j => Disjoint (K i).edgeSet (K j).edgeSet) ∧
    (∀ i, Disjoint (K i).edgeSet E) ∧
    ((⋃ i, (K i).edgeSet) ∪ E = G.edgeSet) := by
  dsimp only
  have hh := complementary_reservoir_graphs (G.deleteEdges E) W hW
  refine ⟨hh.2.2.1,?_,?_⟩
  · intro i
    apply Set.disjoint_left.mpr
    intro e he he'
    have h := SimpleGraph.edgeSet_mono (hh.1 i) he
    rw [SimpleGraph.edgeSet_deleteEdges] at h
    exact h.2 he'
  · rw [hh.2.2.2, SimpleGraph.edgeSet_deleteEdges]
    exact Set.sdiff_union_of_subset hE

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

def edgeRestriction {V : Type cycleUniverse22} (G : SimpleGraph V) (E : Set (Sym2 V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ s(x,y) ∈ E
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact G.loopless.irrefl x h.1⟩

lemma edgeRestriction_le {V : Type cycleUniverse23} (G : SimpleGraph V) (E : Set (Sym2 V)) :
    edgeRestriction G E ≤ G := fun _ _ h => h.1

lemma edgeRestriction_edges {V : Type cycleUniverse24} (G : SimpleGraph V) (E : Set (Sym2 V)) :
    (edgeRestriction G E).edgeSet = G.edgeSet ∩ E := by
  ext e
  induction e using Sym2.ind with | _ x y => rfl

lemma edgeRestriction_edges_of_subset {V : Type cycleUniverse25} (G : SimpleGraph V) (E : Set (Sym2 V))
    (hE : E ⊆ G.edgeSet) : (edgeRestriction G E).edgeSet = E := by
  rw [edgeRestriction_edges, Set.inter_eq_right.mpr hE]

def completedEdges {V : Type cycleUniverse26} {I : Type cycleUniverse27} (C : I → Set (Sym2 V)) : Set (Sym2 V) := ⋃ i, C i

def residualInternalGraph {V : Type cycleUniverse28} {B : Type cycleUniverse29} {I : Type cycleUniverse30} (G : SimpleGraph V)
    (R : B → Set (Sym2 V)) (C : I → Set (Sym2 V)) (b : B) : SimpleGraph V :=
  edgeRestriction G (R b \ completedEdges C)

def unusedSpokes {V : Type cycleUniverse31} {I : Type cycleUniverse32} [Fintype V] (S : Set (Sym2 V))
    (C : I → Set (Sym2 V)) : Finset (Sym2 V) := (S \ completedEdges C).toFinset

lemma unusedSpokes_card_le {V : Type cycleUniverse33} {I : Type cycleUniverse34} [Fintype V] (S : Finset (Sym2 V))
    (C : I → Set (Sym2 V)) : (unusedSpokes (↑S) C).card ≤ S.card := by
  apply Finset.card_le_card
  intro e he
  simp only [unusedSpokes, Set.mem_toFinset, Finset.mem_coe, Set.mem_sdiff] at he
  exact he.1

theorem residue_edge_ledger {V : Type cycleUniverse35} {B : Type cycleUniverse36} {I : Type cycleUniverse37} [Fintype V]
    (G : SimpleGraph V) (R : B → Set (Sym2 V)) (S : Set (Sym2 V))
    (C : I → Set (Sym2 V))
    (hR : ∀ b, R b ⊆ G.edgeSet) (hS : S ⊆ G.edgeSet)
    (hRR : Pairwise fun b c => Disjoint (R b) (R c))
    (hRS : ∀ b, Disjoint (R b) S)
    (hC : ∀ i, C i ⊆ G.edgeSet)
    (_hCC : Pairwise fun i j => Disjoint (C i) (C j))
    (hcover : G.edgeSet \ ((⋃ b, R b) ∪ S) ⊆ completedEdges C) :
    (∀ b, (residualInternalGraph G R C b).edgeSet = R b \ completedEdges C) ∧
    Pairwise (fun b c => Disjoint (residualInternalGraph G R C b).edgeSet
      (residualInternalGraph G R C c).edgeSet) ∧
    (∀ b i, Disjoint (residualInternalGraph G R C b).edgeSet (C i)) ∧
    (∀ b, Disjoint (residualInternalGraph G R C b).edgeSet (↑(unusedSpokes S C) : Set _)) ∧
    (∀ i, Disjoint (C i) (↑(unusedSpokes S C) : Set _)) ∧
    (completedEdges C ∪ (↑(unusedSpokes S C) : Set _) ∪
      (⋃ b, (residualInternalGraph G R C b).edgeSet)) = G.edgeSet := by
  classical
  have hrem (b : B) : (residualInternalGraph G R C b).edgeSet = R b \ completedEdges C := by
    apply edgeRestriction_edges_of_subset
    exact fun e he => hR b he.1
  have hsingle : (↑(unusedSpokes S C) : Set _) = S \ completedEdges C := by
    simp only [unusedSpokes, Set.coe_toFinset]
  have hsub : completedEdges C ⊆ G.edgeSet := by
    rintro e he
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    exact hC i hi
  refine ⟨hrem,?_,?_,?_,?_,?_⟩
  · intro b c hbc
    rw [hrem b,hrem c]
    exact (hRR hbc).mono Set.sdiff_subset Set.sdiff_subset
  · intro b i
    rw [hrem b]
    apply Set.disjoint_left.mpr
    intro e he hi
    exact he.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
  · intro b
    rw [hrem b,hsingle]
    exact (hRS b).mono Set.sdiff_subset Set.sdiff_subset
  · intro i
    rw [hsingle]
    apply Set.disjoint_left.mpr
    intro e hi he
    exact he.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
  · rw [hsingle]
    ext e
    constructor
    · rintro ((he | he) | he)
      · exact hsub he
      · exact hS he.1
      · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp he
        rw [hrem b] at hb
        exact hR b hb.1
    · intro he
      by_cases hc : e ∈ completedEdges C
      · exact Or.inl (Or.inl hc)
      by_cases hs : e ∈ S
      · exact Or.inl (Or.inr ⟨hs,hc⟩)
      have hr : e ∈ ⋃ b, R b := by
        by_contra hr
        exact hc (hcover ⟨he,by intro hu; exact hu.elim hr hs⟩)
      obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hr
      exact Or.inr (Set.mem_iUnion.mpr ⟨b,by rw [hrem b]; exact ⟨hb,hc⟩⟩)

theorem residue_part_count {V : Type cycleUniverse38} {I : Type cycleUniverse39} [Fintype V] [Fintype I]
    (S : Finset (Sym2 V)) (C : I → Set (Sym2 V))
    (hI : Fintype.card I ≤ 3 * Fintype.card V)
    (hS : S.card ≤ 6 * Fintype.card V) :
    Fintype.card I + (unusedSpokes (↑S) C).card ≤ 9 * Fintype.card V := by
  have := unusedSpokes_card_le S C
  omega

lemma induce_edge_image_of_support_subset {V : Type cycleUniverse40} (H : SimpleGraph V)
    (W : Set V) (hW : H.support ⊆ W) :
    Sym2.map Subtype.val '' (H.induce W).edgeSet = H.edgeSet := by
  ext e
  constructor
  · rintro ⟨d,hd,rfl⟩
    induction d using Sym2.ind with
    | _ x y => exact hd
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ∈ W := hW ⟨y,he⟩
      have hy : y ∈ W := hW ⟨x,he.symm⟩
      exact ⟨s(⟨x,hx⟩,⟨y,hy⟩),he,rfl⟩

theorem residual_induce_exact {V : Type cycleUniverse41} {B : Type cycleUniverse42} {I : Type cycleUniverse43} (G : SimpleGraph V)
    (R : B → Set (Sym2 V)) (C : I → Set (Sym2 V)) (b : B) (W : Set V)
    (hR : R b ⊆ G.edgeSet) (hinside : ∀ e ∈ R b, ∀ v ∈ e, v ∈ W) :
    Sym2.map Subtype.val '' ((residualInternalGraph G R C b).induce W).edgeSet =
      R b \ completedEdges C := by
  have hsupport : (residualInternalGraph G R C b).support ⊆ W := by
    rintro v ⟨w,hw⟩
    exact hinside s(v,w) hw.2.1 v (by simp)
  rw [induce_edge_image_of_support_subset _ W hsupport]
  exact edgeRestriction_edges_of_subset G _ (fun e he => hR he.1)

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma walk_edges_internal {V : Type cycleUniverse44} {G P : SimpleGraph V} {a b : V}
    (W : Set V) (q : G.Walk a b) (he : q.edgeSet ⊆ P.edgeSet)
    (hv : ∀ v ∈ q.support, v ∈ W) :
    q.edgeSet ⊆ reservoirInternal P W := by
  intro e h
  refine ⟨he h,?_⟩
  induction e using Sym2.ind with
  | _ x y =>
    intro v hmem
    rcases (Sym2.mem_iff.mp hmem) with rfl | rfl
    · exact hv _ (q.fst_mem_support_of_mem_edges h)
    · exact hv _ (q.snd_mem_support_of_mem_edges h)

lemma completion_edges_subset {V : Type cycleUniverse45} [Fintype V] [DecidableEq V]
    {G P : SimpleGraph V} (W : Finset V) (r : V × Fin 2 → V)
    {x y a b : V} (Q : G.Walk x y) (q : G.Walk a b) (C : G.Walk x x)
    (K : Set (Sym2 V)) (hQ : Q.edgeSet ⊆ K)
    (hC : C.edgeSet = Q.edgeSet ∪ q.edgeSet ∪ {s(x,a),s(y,b)})
    (hq : q.edgeSet ⊆ P.edgeSet ∧ ∀ v ∈ q.support, v ∈ W)
    (hx : x ∉ W) (hy : y ∉ W)
    (ha : ∃ t, a = r (x,t)) (hb : ∃ t, b = r (y,t)) :
    C.edgeSet ⊆ K ∪ (reservoirInternal P W ∪ (reservoirSpokes W r : Set _)) := by
  rw [hC]
  have hqi := walk_edges_internal (W : Set V) q hq.1 hq.2
  intro e he
  rcases he with (he | he) | he
  · exact Or.inl (hQ he)
  · exact Or.inr (Or.inl (hqi he))
  · apply Or.inr ∘ Or.inr
    rcases (show e = s(x,a) ∨ e = s(y,b) by simpa using he) with rfl | rfl
    · obtain ⟨t,rfl⟩ := ha
      exact (mem_reservoirSpokes W r _).mpr ⟨x,hx,t,rfl⟩
    · obtain ⟨t,rfl⟩ := hb
      exact (mem_reservoirSpokes W r _).mpr ⟨y,hy,t,rfl⟩

lemma completed_subfamilies_disjoint {E : Type cycleUniverse46} {B : Type cycleUniverse47} {I : B → Type cycleUniverse55}
    (K R : B → Set E) (C : ∀ b, I b → Set E)
    (hKK : Pairwise fun b c => Disjoint (K b) (K c))
    (hRR : Pairwise fun b c => Disjoint (R b) (R c))
    (hKR : ∀ b c, Disjoint (K b) (R c))
    (hC : ∀ b i, C b i ⊆ K b ∪ R b)
    (hCC : ∀ b, Pairwise fun i j => Disjoint (C b i) (C b j)) :
    Pairwise (fun s t : Sigma I => Disjoint (C s.1 s.2) (C t.1 t.2)) := by
  rintro ⟨b,i⟩ ⟨c,j⟩ hne
  by_cases hbc : b = c
  · subst c
    apply hCC b
    intro hij
    exact hne (by cases hij; rfl)
  · apply Disjoint.mono (hC b i) (hC c j)
    rw [Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
    exact ⟨⟨hKK hbc,hKR b c⟩,⟨(hKR c b).symm,hRR hbc⟩⟩

lemma completed_subfamilies_cover {E : Type cycleUniverse48} {B : Type cycleUniverse49} {I : B → Type cycleUniverse56}
    (K : B → Set E) (Q C : ∀ b, I b → Set E)
    (hQ : ∀ b, (⋃ i, Q b i) = K b)
    (hQC : ∀ b i, Q b i ⊆ C b i) :
    (⋃ b, K b) ⊆ ⋃ s : Sigma I, C s.1 s.2 := by
  intro e he
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp he
  rw [← hQ b] at hb
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hb
  exact Set.mem_iUnion.mpr ⟨⟨b,i⟩,hQC b i hi⟩

lemma endpointLoad_family_card {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (hload : ∀ v, endpointLoad univ x y v ≤ 2) :
    Fintype.card I ≤ Fintype.card V := by
  classical
  have hs := endpointLoad_sum (univ : Finset I) x y (fun i _ => hne i)
  have hb := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hload v)
  simp only [Finset.card_univ] at hs
  rw [hs] at hb
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hb
  omega

lemma sigma_three_card_le {V : Type} [Fintype V]
    (I : Fin 3 → Type) [∀ b, Fintype (I b)]
    (hI : ∀ b, Fintype.card (I b) ≤ Fintype.card V) :
    Fintype.card (Sigma I) ≤ 3 * Fintype.card V := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _b : Fin 3, Fintype.card V := Finset.sum_le_sum (fun b _ => hI b)
    _ = _ := by simp [mul_comm]

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

theorem uniform_three_reservoir_completion (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G : SimpleGraph V) (P K : Fin 3 → SimpleGraph V)
        [∀ b, DecidableRel (P b).Adj],
      (∀ b, P b ≤ G) →
      Pairwise (fun b d => Disjoint (P b).edgeSet (P d).edgeSet) →
      ∀ (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V),
      (∀ b, CutExpansionOn (P b) (W b) (D^(37/50:ℝ))) →
      (∀ b, 2 ≤ (W b).card) → (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      (∀ b v, v ∉ W b → ∀ t, r b (v,t) ∈ W b ∧ (P b).Adj v (r b (v,t))) →
      (∀ b v, v ∉ W b → r b (v,0) ≠ r b (v,1)) →
      (∀ b v, (((W b)ᶜ ×ˢ univ).filter (fun z => r b z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      let T := fun b => reservoirInternal (P b) (W b) ∪
        (reservoirSpokes (W b) (r b) : Set (Sym2 V))
      Pairwise (fun b d => Disjoint (K b).edgeSet (K d).edgeSet) →
      (∀ b d, Disjoint (K b).edgeSet (T d)) →
      ∀ (I : Fin 3 → Type) [∀ b, Fintype (I b)]
        (x y : ∀ b, I b → V) (Q : ∀ b i, G.Walk (x b i) (y b i)),
      (∀ b i, (Q b i).IsPath) → (∀ b i, 0 < (Q b i).length) →
      (∀ b i v, v ∈ (Q b i).support → v ∉ W b) →
      (∀ b, Pairwise fun i j => Disjoint (Q b i).edgeSet (Q b j).edgeSet) →
      (∀ b, (⋃ i, (Q b i).edgeSet) = (K b).edgeSet) →
      (∀ b v, endpointLoad univ (x b) (y b) v ≤ 2) →
      ∃ C : ∀ b i, G.Walk (x b i) (x b i),
        (∀ b i, (C b i).IsCycle) ∧
        Pairwise (fun s t : Sigma I =>
          Disjoint (C s.1 s.2).edgeSet (C t.1 t.2).edgeSet) ∧
        (∀ b i, (C b i).edgeSet ⊆ (K b).edgeSet ∪ T b) ∧
        (⋃ b, (K b).edgeSet) ⊆ (⋃ s : Sigma I, (C s.1 s.2).edgeSet) ∧
        Fintype.card (Sigma I) ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨D₀,hD₀,hclose⟩ := uniform_reservoir_completion c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P K _ hPG hPP W r hexp hW hn hr hrne hcap
  dsimp only
  intro hKK hKT I _ x y Q hQ hpos hout hQQ hcover hl
  have hex : ∀ b : Fin 3,
      ∃ (a z : I b → V) (q : ∀ i, G.Walk (a i) (z i))
        (C : ∀ i, G.Walk (x b i) (x b i)),
        (∀ i, (C i).IsCycle) ∧
        Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
        (∀ i, (C i).edgeSet = (Q b i).edgeSet ∪ (q i).edgeSet ∪
          {s(x b i,a i),s(y b i,z i)}) ∧
        (∀ i, (q i).edgeSet ⊆ (P b).edgeSet ∧ ∀ v ∈ (q i).support, v ∈ W b) ∧
        Function.Injective (fun z' : I b × Fin 2 =>
          if z'.2 = 0 then s(x b z'.1,a z'.1) else s(y b z'.1,z z'.1)) ∧
        (∀ i, ∃ t, a i = r b (x b i,t)) ∧
        (∀ i, ∃ t, z i = r b (y b i,t)) := by
    intro b
    exact hclose D hD V G (P b) (hPG b) (W b) (hexp b) (hW b) hn
      (I b) (x b) (y b) (Q b) (hQ b) (hpos b) (hout b) (hQQ b) (hl b)
      (r b) (hr b) (hrne b) (hcap b)
  choose a z q C hCy hCC hCe hqe _hsp ha hz using hex
  have hsub : ∀ b i, (C b i).edgeSet ⊆ (K b).edgeSet ∪
      (reservoirInternal (P b) (W b) ∪ (reservoirSpokes (W b) (r b) : Set _)) := by
    intro b i
    apply completion_edges_subset (W b) (r b) (Q b i) (q b i) (C b i)
      (K b).edgeSet _ (hCe b i) (hqe b i)
      (hout b i _ (Q b i).start_mem_support)
      (hout b i _ (Q b i).end_mem_support) (ha b i) (hz b i)
    intro e he
    rw [← hcover b]
    exact Set.mem_iUnion.mpr ⟨i,he⟩
  have hreserv := reservoir_reservations G P W r hPG hPP
    (fun b v hv t => (hr b v hv t).2)
  refine ⟨C,hCy,?_,hsub,?_,?_⟩
  · exact completed_subfamilies_disjoint (fun b => (K b).edgeSet)
      (fun b => reservoirInternal (P b) (W b) ∪
        (reservoirSpokes (W b) (r b) : Set _))
      (fun b i => (C b i).edgeSet) hKK hreserv.2.1 hKT hsub hCC
  · apply completed_subfamilies_cover (fun b => (K b).edgeSet)
      (fun b i => (Q b i).edgeSet) (fun b i => (C b i).edgeSet) hcover
    intro b i e he
    rw [hCe b i]
    exact Or.inl (Or.inl he)
  · apply sigma_three_card_le I
    intro b
    apply endpointLoad_family_card (x b) (y b) _ (hl b)
    intro i hi
    have hz := ((hQ b i).nil_iff_eq.mpr hi).length_eq_zero
    have hp := hpos b i
    omega

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

noncomputable def allReservoirSpokes {V : Type cycleUniverse50} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) : Finset (Sym2 V) :=
  univ.biUnion (fun b => reservoirSpokes (W b) (r b))

lemma coe_allReservoirSpokes {V : Type cycleUniverse51} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) :
    (allReservoirSpokes W r : Set (Sym2 V)) =
      ⋃ b, (reservoirSpokes (W b) (r b) : Set (Sym2 V)) := by
  ext e
  simp [allReservoirSpokes]

lemma allReservoirSpokes_card_le {V : Type cycleUniverse52} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) :
    (allReservoirSpokes W r).card ≤ 6 * Fintype.card V := by
  apply (Finset.card_biUnion_le).trans
  calc
    (∑ b : Fin 3, (reservoirSpokes (W b) (r b)).card) ≤
      ∑ _b : Fin 3, 2 * Fintype.card V :=
        Finset.sum_le_sum (fun b _ => reservoirSpokes_card_le (W b) (r b))
    _ = _ := by simp; omega

theorem three_reservoir_remainder {V : Type cycleUniverse53} {I : Type cycleUniverse54} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (P : Fin 3 → SimpleGraph V)
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V)
    (hPG : ∀ b, P b ≤ G)
    (hPP : Pairwise fun b d => Disjoint (P b).edgeSet (P d).edgeSet)
    (hr : ∀ b v, v ∉ W b → ∀ t, (P b).Adj v (r b (v,t)))
    (C : I → Set (Sym2 V)) (hC : ∀ i, C i ⊆ G.edgeSet)
    (hCC : Pairwise fun i j => Disjoint (C i) (C j))
    (hI : Fintype.card I ≤ 3 * Fintype.card V)
    (hcover : G.edgeSet \ ((⋃ b, reservoirInternal (P b) (W b)) ∪
      (allReservoirSpokes W r : Set _)) ⊆ completedEdges C) :
    let R := fun b => reservoirInternal (P b) (W b)
    let H := residualInternalGraph G R C
    let S := unusedSpokes (↑(allReservoirSpokes W r)) C
    (∀ b, (H b).support ⊆ (W b : Set V)) ∧
    (∀ b, Sym2.map Subtype.val '' ((H b).induce (W b : Set V)).edgeSet = (H b).edgeSet) ∧
    (∀ b, (H b).edgeSet = R b \ completedEdges C) ∧
    Pairwise (fun b d => Disjoint (H b).edgeSet (H d).edgeSet) ∧
    (∀ b i, Disjoint (H b).edgeSet (C i)) ∧
    (∀ b, Disjoint (H b).edgeSet (S : Set _)) ∧
    (∀ i, Disjoint (C i) (S : Set _)) ∧
    (completedEdges C ∪ (S : Set _) ∪ (⋃ b, (H b).edgeSet)) = G.edgeSet ∧
    Fintype.card I + S.card ≤ 9 * Fintype.card V := by
  classical
  dsimp only
  obtain ⟨hsub,hTT,_hown,hRS,_hcount⟩ := reservoir_reservations G P W r hPG hPP hr
  have hS : (allReservoirSpokes W r : Set (Sym2 V)) ⊆ G.edgeSet := by
    rw [coe_allReservoirSpokes]
    exact Set.iUnion_subset (fun b => (hsub b).2)
  have hRR : Pairwise fun b d =>
      Disjoint (reservoirInternal (P b) (W b)) (reservoirInternal (P d) (W d)) := by
    intro b d hbd
    exact (hTT hbd).mono Set.subset_union_left Set.subset_union_left
  have hRO : ∀ b, Disjoint (reservoirInternal (P b) (W b))
      (allReservoirSpokes W r : Set (Sym2 V)) := by
    intro b
    rw [coe_allReservoirSpokes]
    exact hRS.mono_left (Set.subset_iUnion (fun d => reservoirInternal (P d) (W d)) b)
  let R := fun b => reservoirInternal (P b) (W b)
  let H := residualInternalGraph G R C
  have hledger := residue_edge_ledger G R (↑(allReservoirSpokes W r)) C
    (fun b => (hsub b).1) hS hRR hRO hC hCC hcover
  have hsupp : ∀ b, (H b).support ⊆ (W b : Set V) := by
    intro b v hv
    obtain ⟨w,hw⟩ := (H b).mem_support.mp hv
    have he : s(v,w) ∈ (H b).edgeSet := hw
    rw [hledger.1 b] at he
    exact he.1.2 _ (Sym2.mem_mk_left _ _)
  refine ⟨hsupp,?_,hledger.1,hledger.2.1,hledger.2.2.1,
    hledger.2.2.2.1,hledger.2.2.2.2.1,hledger.2.2.2.2.2,?_⟩
  · intro b
    exact induce_edge_image_of_support_subset (H b) (W b) (hsupp b)
  · exact residue_part_count (allReservoirSpokes W r) C hI (allReservoirSpokes_card_le W r)

end
end ErdosGallai

end
end
end

end OAI
