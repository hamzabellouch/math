import OAI.Combinatorics.CycleDecomposition.CycleLifting

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

def demandLoad {I : Type cycleUniverse1} {V : Type cycleUniverse2} [Fintype I] (x y : I → V) (v : V) : ℕ :=
  (univ.filter fun i => x i = v ∨ y i = v).card

theorem demand_load_le_degree {V : Type cycleUniverse3} {I : Type cycleUniverse4} {B : Type cycleUniverse5} [Fintype V] [Fintype I]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : B → Set (Sym2 V))
    (hE : Pairwise fun b c => Disjoint (E b) (E c))
    (owner : I → B) (x y : I → V)
    (hunique : ∀ i j v, owner i = owner j →
      (x i = v ∨ y i = v) → (x j = v ∨ y j = v) → i = j)
    (hedge : ∀ i v, x i = v ∨ y i = v →
      ∃ w, G.Adj v w ∧ s(v,w) ∈ E (owner i)) (v : V) :
    demandLoad x y v ≤ G.degree v := by
  classical
  let S := {i : I // x i = v ∨ y i = v}
  have hs (i : S) := hedge i.val v i.property
  let f : S → G.neighborFinset v := fun i =>
    ⟨(hs i).choose, by simpa using (hs i).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he : (hs i).choose = (hs j).choose := congrArg Subtype.val hij
    apply Subtype.ext
    by_cases ho : owner i.val = owner j.val
    · exact hunique i.val j.val v ho i.property j.property
    · exact False.elim (Set.disjoint_left.mp (hE ho)
        (hs i).choose_spec.2 (by rw [he]; exact (hs j).choose_spec.2))
  have hc := Fintype.card_le_of_injective f hf
  have hn : Fintype.card (G.neighborFinset v) = G.degree v := by
    rw [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree]
  rw [hn] at hc
  have hcS : Fintype.card S = demandLoad x y v := by
    simp only [S, Fintype.card_subtype, demandLoad]
    congr 1
    ext i
    simp
  rw [hcS] at hc
  exact hc

lemma start_has_incident_edge {V : Type cycleUniverse6} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ¬p.Nil) :
    ∃ w, G.Adj a w ∧ s(a,w) ∈ p.edgeSet := by
  exact ⟨p.snd,p.adj_snd hp,p.mk_start_snd_mem_edges hp⟩

lemma finish_has_incident_edge {V : Type cycleUniverse7} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ¬p.Nil) :
    ∃ w, G.Adj b w ∧ s(b,w) ∈ p.edgeSet := by
  refine ⟨p.penultimate,(p.adj_penultimate hp).symm,?_⟩
  change s(b,p.penultimate) ∈ p.edges
  simpa only [Sym2.eq_swap] using p.mk_penultimate_end_mem_edges hp

theorem path_demands_load_le_degree {V : Type cycleUniverse8} {I : Type cycleUniverse9} [Fintype V] [Fintype I]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : I → V) (p : ∀ i, G.Walk (x i) (y i))
    (hpos : ∀ i, ¬(p i).Nil)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet) (v : V) :
    demandLoad x y v ≤ G.degree v := by
  apply demand_load_le_degree G (fun i => (p i).edgeSet) hd id x y
  · intro i j _ hij _ _; exact hij
  · intro i w hw
    rcases hw with rfl | rfl
    · exact start_has_incident_edge (p i) (hpos i)
    · exact finish_has_incident_edge (p i) (hpos i)

lemma disjoint_sum_blocks {α : Type cycleUniverse10} {B : Type cycleUniverse11} {C : Type cycleUniverse12} (E : B → Set α) (F : C → Set α)
    (hE : Pairwise fun b c => Disjoint (E b) (E c))
    (hF : Pairwise fun b c => Disjoint (F b) (F c))
    (hEF : ∀ b c, Disjoint (E b) (F c)) :
    Pairwise (fun i j : B ⊕ C => Disjoint (Sum.elim E F i) (Sum.elim E F j)) := by
  intro i j hij
  cases i with
  | inl b =>
    cases j with
    | inl c => exact hE (fun he => hij (congrArg Sum.inl he))
    | inr c => exact hEF b c
  | inr b =>
    cases j with
    | inl c => exact (hEF c b).symm
    | inr c => exact hF (fun he => hij (congrArg Sum.inr he))

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch

def CycleOrSingleEdge {V : Type} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet) ∨
  ∃ e ∈ G.edgeSet, s = {e}

def EdgeDecomposition {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ parts : Fin k → Set (Sym2 V),
    (∀ i, CycleOrSingleEdge G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet

noncomputable section
open SimpleGraph

lemma cycleOrSingleEdge_subset {V : Type} {G : SimpleGraph V}
    {s : Set (Sym2 V)} (hs : CycleOrSingleEdge G s) : s ⊆ G.edgeSet := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact p.edges_subset_edgeSet
  · simpa using he

lemma cycleOrSingleEdge_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {s : Set (Sym2 V)}
    (hs : CycleOrSingleEdge G s) : CycleOrSingleEdge H (Sym2.map f '' s) := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact Or.inl ⟨f v,p.map f,hp.map hf,(p.edgeSet_map f).symm⟩
  · refine Or.inr ⟨Sym2.map f e, ?_, by simp⟩
    induction e using Sym2.ind with | _ x y =>
      exact f.map_adj he

lemma edgeDecomposition_of_indexed {V I : Type} [Fintype I] (G : SimpleGraph V)
    (parts : I → Set (Sym2 V)) (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hu : (⋃ i, parts i) = G.edgeSet) : EdgeDecomposition G (Fintype.card I) := by
  let e := Fintype.equivFin I
  refine ⟨fun j => parts (e.symm j), fun j => hp _, ?_, ?_⟩
  · intro i j hij
    exact hd (fun he => hij (e.symm.injective he))
  · ext x
    simp only [Set.mem_iUnion]
    rw [← hu]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e i, by simpa using hi⟩

theorem edgeDecomposition_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (Nat.card G.edgeSet) := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  apply edgeDecomposition_of_indexed G (fun e : G.edgeSet => {e.1})
  · intro e; exact Or.inr ⟨e.1,e.2,rfl⟩
  · intro e d hed
    exact Set.disjoint_singleton.mpr (fun h => hed (Subtype.ext h))
  · ext e; simp

theorem edgeDecomposition_assemble {V I : Type} [Fintype I] (G : SimpleGraph V)
    (W : I → Type) (H : ∀ i, SimpleGraph (W i))
    (f : ∀ i, H i →g G) (hf : ∀ i, Function.Injective (f i))
    (hdisj : Pairwise (fun i j =>
      Disjoint (Sym2.map (f i) '' (H i).edgeSet) (Sym2.map (f j) '' (H j).edgeSet)))
    (hcover : (⋃ i, Sym2.map (f i) '' (H i).edgeSet) = G.edgeSet)
    (k : I → ℕ) (hparts : ∀ i, EdgeDecomposition (H i) (k i)) :
    EdgeDecomposition G (∑ i, k i) := by
  classical
  choose parts hp hd hu using hparts
  let J := Σ i, Fin (k i)
  let P : J → Set (Sym2 V) := fun j => Sym2.map (f j.1) '' parts j.1 j.2
  have hpart : ∀ j, CycleOrSingleEdge G (P j) := by
    intro j; exact cycleOrSingleEdge_map (f j.1) (hf j.1) (hp j.1 j.2)
  have hsub : ∀ i a, parts i a ⊆ (H i).edgeSet := by
    intro i a; exact cycleOrSingleEdge_subset (hp i a)
  have hdisjP : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hij
    by_cases h : i = j
    · subst j
      have hab : a ≠ b := fun he => hij (by cases he; rfl)
      apply Set.disjoint_left.mpr
      rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
      have hxy : x = y := Sym2.map.injective (hf i) (he.trans he'.symm)
      subst y
      exact Set.disjoint_left.mp (hd i hab) hx hy
    · exact (hdisj h).mono (Set.image_mono (hsub i a)) (Set.image_mono (hsub j b))
  have hcoverP : (⋃ j, P j) = G.edgeSet := by
    rw [← hcover]
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i,a⟩,x,hx,he⟩
      exact ⟨i,x,hsub i a hx,he⟩
    · rintro ⟨i,x,hx,he⟩
      rw [← hu i] at hx
      obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i,a⟩,x,ha,he⟩
  have hc : Fintype.card J = ∑ i, k i := by simp [J, Fintype.card_sigma]
  rw [← hc]
  exact edgeDecomposition_of_indexed G P hpart hdisjP hcoverP

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

def decompositionCost {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (show ∃ k, EdgeDecomposition G k from ⟨_,edgeDecomposition_singleEdges G⟩)

lemma decompositionCost_spec {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (decompositionCost G) := Nat.find_spec _

lemma decompositionCost_le {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : EdgeDecomposition G k) : decompositionCost G ≤ k := Nat.find_min' _ h

lemma decompositionCost_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G ≤ Nat.card G.edgeSet := decompositionCost_le (edgeDecomposition_singleEdges G)

theorem edgeDecomposition_adjoin {V I J : Type} [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) (H : ∀ j, SimpleGraph (W j)) (f : ∀ j, H j →g G)
    (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet)
    (k : J → ℕ) (hD : ∀ j, EdgeDecomposition (H j) (k j)) :
    EdgeDecomposition G (Fintype.card I + ∑ j, k j) := by
  classical
  choose P hP hPd hPc using hD
  let R : (I ⊕ Σ j, Fin (k j)) → Set (Sym2 V) :=
    Sum.elim parts (fun z => Sym2.map (f z.1) '' P z.1 z.2)
  have hsub : ∀ j i, P j i ⊆ (H j).edgeSet := fun j i => cycleOrSingleEdge_subset (hP j i)
  have hRp : ∀ z, CycleOrSingleEdge G (R z) := by
    intro z
    rcases z with z | ⟨j,i⟩
    · exact hp z
    · exact cycleOrSingleEdge_map (f j) (hf j) (hP j i)
  have hRd : Pairwise fun z t => Disjoint (R z) (R t) := by
    intro z t hzt
    rcases z with z | ⟨j,i⟩ <;> rcases t with t | ⟨l,a⟩
    · exact hd (fun h => hzt (congrArg Sum.inl h))
    · exact ((hHP l z).mono_left (Set.image_mono (hsub l a))).symm
    · exact (hHP j t).mono_left (Set.image_mono (hsub j i))
    · by_cases hjl : j = l
      · subst l
        have hia : i ≠ a := fun h => hzt (by cases h; rfl)
        apply Set.disjoint_left.mpr
        rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
        have hxy := Sym2.map.injective (hf j) (he.trans he'.symm)
        subst y
        exact Set.disjoint_left.mp (hPd j hia) hx hy
      · exact (hHH hjl).mono (Set.image_mono (hsub j i)) (Set.image_mono (hsub l a))
  have hRu : (⋃ z, R z) = G.edgeSet := by
    rw [← hu]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨z,hz⟩
      rcases z with z | ⟨j,i⟩
      · exact Or.inl ⟨z,hz⟩
      · obtain ⟨x,hx,he⟩ := hz
        exact Or.inr ⟨j,x,hsub j i hx,he⟩
    · rintro (⟨i,hi⟩ | ⟨j,x,hx,he⟩)
      · exact ⟨Sum.inl i,hi⟩
      · rw [← hPc j] at hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨j,i⟩,x,hi,he⟩
  simpa only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] using
    edgeDecomposition_of_indexed G R hRp hRd hRu

lemma decompositionCost_adjoin {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) [∀ j, Fintype (W j)] (H : ∀ j, SimpleGraph (W j))
    (f : ∀ j, H j →g G) (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) :=
  decompositionCost_le (edgeDecomposition_adjoin G parts hp hd W H f hf hHH hHP hu _
    (fun j => decompositionCost_spec (H j)))

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma edgeDecomposition_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H →g G) (hf : Function.Injective f)
    (hu : Sym2.map f '' H.edgeSet = G.edgeSet) {k : ℕ} (hk : EdgeDecomposition H k) :
    EdgeDecomposition G k := by
  have := edgeDecomposition_assemble (I := Unit) G (fun _ : Unit => W) (fun _ => H) (fun _ => f)
    (fun _ => hf) (by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)))
    (by rw [Set.iUnion_const]; exact hu) (fun _ => k) (fun _ => hk)
  simpa using this

lemma decompositionCost_on {V : Type} [Fintype V] (G : SimpleGraph V)
    (A : Finset V) (hA : ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A) :
    decompositionCost G ≤ decompositionCost (G.induce (A:Set V)) := by
  classical
  let f : G.induce (A:Set V) →g G := ⟨Subtype.val,fun h => h⟩
  have hu : Sym2.map f '' (G.induce (A:Set V)).edgeSet = G.edgeSet := by
    ext e
    constructor
    · rintro ⟨e,he,rfl⟩
      induction e using Sym2.ind with | _ x y => exact he
    · intro he
      induction e using Sym2.ind with
      | _ x y =>
        exact ⟨s(⟨x,(hA he).1⟩,⟨y,(hA he).2⟩),he,rfl⟩
  exact decompositionCost_le (edgeDecomposition_map f Subtype.val_injective hu (decompositionCost_spec _))

lemma edgeDecomposition_on {V : Type} (G : SimpleGraph V)
    (A : Finset V) (hA : ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A)
    {k : ℕ} (hk : EdgeDecomposition (G.induce (A:Set V)) k) : EdgeDecomposition G k := by
  classical
  let f : G.induce (A:Set V) →g G := ⟨Subtype.val,fun h => h⟩
  apply edgeDecomposition_map f Subtype.val_injective _ hk
  ext e
  constructor
  · rintro ⟨e,he,rfl⟩
    induction e using Sym2.ind with | _ x y => exact he
  · intro he
    induction e using Sym2.ind with
    | _ x y => exact ⟨s(⟨x,(hA he).1⟩,⟨y,(hA he).2⟩),he,rfl⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma endpointLoad_subtype_le {V I : Type} [Fintype I]
    (x y : I → V) (s : I → Prop) (v : V) :
    endpointLoad univ (fun i : {i // s i} => x i) (fun i => y i) v ≤ endpointLoad univ x y v := by
  classical
  simp only [endpointLoad]
  apply Finset.card_le_card_of_injOn (fun i : {i // s i} => i.val)
  · intro i hi; simpa using hi
  · intro i _ j _ h; exact Subtype.ext h

theorem uniform_multi_batch_routing :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V R I T : Type) [Fintype V] [Fintype R] [Fintype I],
      ∀ (G : SimpleGraph V) (P : R → SimpleGraph V) (U : R → Finset V),
      (∀ r, P r ≤ G) → Pairwise (fun r s => Disjoint (P r).edgeSet (P s).edgeSet) →
      Pairwise (fun r s => Disjoint (U r) (U s)) →
      (∀ r, CutExpansionOn (P r) (U r) (D^(9/10:ℝ)/4)) →
      (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
      ∀ (owner : I → R) (x y : I → V),
      (∀ i, x i ∈ U (owner i) ∧ y i ∈ U (owner i) ∧ x i ≠ y i) →
      ∀ (team : I → T) (Z : I → Finset V),
      (∀ v, (endpointLoad univ x y v:ℝ) ≤ D^(1/100:ℝ)) →
      (∀ i, ((univ.filter (fun j => team j = team i)).card:ℝ) ≤ D^(3/10:ℝ)) →
      (∀ i, ((Z i).card:ℝ) ≤ 2*D^(3/10:ℝ)) →
      ∃ q : ∀ i, G.Walk (x i) (y i),
        (∀ i, (q i).IsPath ∧ (∀ v ∈ (q i).support, v ∈ U (owner i)) ∧
          (q i).edgeSet ⊆ (P (owner i)).edgeSet ∧ Disjoint (pathInterior (q i)) (Z i)) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
        (∀ i j, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  obtain ⟨D₀,hD₀,hroute⟩ := uniform_batch_routing
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V R I T _ _ _ G P U hPG hPP hUU he hr owner x y hxy team Z hl ht hZ
  let J := fun r => {i // owner i = r}
  have hex : ∀ r, ∃ q : ∀ i : J r, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (∀ v ∈ (q i).support, v ∈ U r) ∧
        (q i).edgeSet ⊆ (P r).edgeSet ∧ Disjoint (pathInterior (q i)) (Z i)) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
      (∀ i j : J r, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
    intro r
    obtain ⟨q,hq,hd,hi⟩ := hroute D hD V G (P r) (hPG r) (U r) (he r) (hr r).1 (hr r).2
      (J r) T (fun i => x i) (fun i => y i)
      (fun i => by simpa only [← i.property] using (hxy i).1)
      (fun i => by simpa only [← i.property] using (hxy i).2.1)
      (fun i => (hxy i).2.2) (fun i => team i) (fun i => Z i)
      (fun v => (show (endpointLoad univ (fun i : J r => x i) (fun i => y i) v:ℝ) ≤
        endpointLoad univ x y v by exact_mod_cast endpointLoad_subtype_le x y (fun i => owner i = r) v).trans (hl v))
      (fun i => le_trans (by
        apply Nat.cast_le.mpr
        apply Finset.card_le_card_of_injOn (fun i : J r => i.val)
        · intro j hj; simpa using hj
        · intro j _ l _ h; exact Subtype.ext h) (ht i)) (fun i => hZ i)
    exact ⟨q,fun i => ⟨(hq i).1,(hq i).2.2⟩,hd,hi⟩
  choose q hq hd hi using hex
  let f : ∀ i, G.Walk (x i) (y i) := fun i => q (owner i) ⟨i,rfl⟩
  have hf (i : I) (r : R) (h : owner i = r) : f i = q r ⟨i,h⟩ := by
    subst r; rfl
  refine ⟨f,fun i => hq _ _,?_,?_⟩
  · intro i j hij
    by_cases hh : owner i = owner j
    · have h := hd (owner i) (show (⟨i,rfl⟩:J (owner i)) ≠ ⟨j,hh.symm⟩ from
        fun h => hij (congrArg Subtype.val h))
      rw [hf j (owner i) hh.symm]
      exact h
    · exact (hPP hh).mono (hq _ _).2.2.1 (hq _ _).2.2.1
  · intro i j hij hteam
    by_cases hh : owner i = owner j
    · have h := hi (owner i) ⟨i,rfl⟩ ⟨j,hh.symm⟩
        (fun h => hij (congrArg Subtype.val h)) hteam
      rw [hf j (owner i) hh.symm]
      exact h
    · apply (hUU hh).mono
      · intro v hv; exact (hq (owner i) ⟨i,rfl⟩).2.1 v (List.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1)
      · intro v hv; exact (hq (owner j) ⟨j,rfl⟩).2.1 v (List.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1)

structure CycleOutline {V : Type} (G : SimpleGraph V) where
  W : Type
  finiteW : Fintype W
  Q : SimpleGraph W
  base : W
  cycle : Q.Walk base base
  isCycle : cycle.IsCycle
  rep : Q.Dart → G.Dart
  start : W → V
  finish : W → V
  project : V → W
  ports : ∀ d ∈ cycle.darts, finish d.fst = (rep d).fst ∧ start d.snd = (rep d).snd
  projects : ∀ z ∈ cycle.dropLast.support, project (start z) = z ∧ project (finish z) = z
  outside : ∀ z, z ∉ cycle.dropLast.support → start z = finish z
attribute [instance] CycleOutline.finiteW

namespace CycleOutline
variable {V : Type} {G : SimpleGraph V} (c : CycleOutline G)

def edges : Set (Sym2 V) := {e | ∃ d ∈ c.cycle.darts, e = (c.rep d).edge}
def vertices : Finset V := c.cycle.darts.toFinset.biUnion fun d => {(c.rep d).fst,(c.rep d).snd}
abbrev Switch := {z : c.W // z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z}
instance : Fintype c.Switch := inferInstanceAs (Fintype {_z : c.W // _})

lemma edges_subset : c.edges ⊆ G.edgeSet := by
  rintro e ⟨d,hd,rfl⟩; exact (c.rep d).edge_mem

lemma fst_mem {d : c.Q.Dart} (hd : d ∈ c.cycle.darts) : d.fst ∈ c.cycle.dropLast.support := by
  rw [c.cycle.support_dropLast c.isCycle.not_nil,← Walk.map_fst_darts]
  exact List.mem_map.mpr ⟨d,hd,rfl⟩

lemma snd_mem {d : c.Q.Dart} (hd : d ∈ c.cycle.darts) : d.snd ∈ c.cycle.dropLast.support := by
  rw [c.cycle.support_dropLast c.isCycle.not_nil]
  apply c.cycle.tail_support_perm_dropLast_support.mem_iff.mp
  rw [← Walk.map_snd_darts]
  exact List.mem_map.mpr ⟨d,hd,rfl⟩

lemma outgoing (z : c.W) (hz : z ∈ c.cycle.dropLast.support) :
    ∃ d ∈ c.cycle.darts, d.fst = z := by
  have h : z ∈ c.cycle.darts.map (fun d => d.fst) := by
    rw [Walk.map_fst_darts,← c.cycle.support_dropLast c.isCycle.not_nil]; exact hz
  exact List.mem_map.mp h

lemma incoming (z : c.W) (hz : z ∈ c.cycle.dropLast.support) :
    ∃ d ∈ c.cycle.darts, d.snd = z := by
  have h : z ∈ c.cycle.darts.map (fun d => d.snd) := by
    rw [Walk.map_snd_darts]
    apply c.cycle.tail_support_perm_dropLast_support.mem_iff.mpr
    rw [← c.cycle.support_dropLast c.isCycle.not_nil]; exact hz
  exact List.mem_map.mp h

lemma endpoint_incident (z : c.Switch) (v : V) (hv : c.start z = v ∨ c.finish z = v) :
    ∃ w, G.Adj v w ∧ s(v,w) ∈ c.edges := by
  rcases hv with rfl | rfl
  · obtain ⟨d,hd,he⟩ := c.incoming z z.property.1
    have hh := (c.ports d hd).2
    rw [he] at hh
    refine ⟨(c.rep d).fst,?_,?_⟩
    · rw [hh]; exact (c.rep d).adj.symm
    · refine ⟨d,hd,?_⟩
      rw [hh]; exact Sym2.eq_swap
  · obtain ⟨d,hd,he⟩ := c.outgoing z z.property.1
    have hh := (c.ports d hd).1
    rw [he] at hh
    refine ⟨(c.rep d).snd,?_,?_⟩
    · rw [hh]; exact (c.rep d).adj
    · refine ⟨d,hd,?_⟩; rw [hh]; rfl

lemma endpoint_unique (z w : c.Switch) (v : V)
    (hz : c.start z = v ∨ c.finish z = v) (hw : c.start w = v ∨ c.finish w = v) : z = w := by
  apply Subtype.ext
  have hf : ∀ (z : c.Switch), c.start z = v ∨ c.finish z = v → c.project v = z := by
    intro z hz
    rcases hz with h | h
    · rw [← h]; exact (c.projects z z.property.1).1
    · rw [← h]; exact (c.projects z z.property.1).2
  exact (hf z hz).symm.trans (hf w hw)

lemma vertices_card_support : c.vertices.card ≤ 2 * c.cycle.dropLast.support.toFinset.card := by
  have hfirst : c.vertices.card ≤ 2*c.cycle.darts.toFinset.card := by
    calc
      _ ≤ ∑ d ∈ c.cycle.darts.toFinset, ({(c.rep d).fst,(c.rep d).snd}:Finset V).card := Finset.card_biUnion_le
      _ ≤ ∑ d ∈ c.cycle.darts.toFinset, 2 := Finset.sum_le_sum (fun d _ => Finset.card_le_two)
      _ = _ := by simp [mul_comm]
  have hd : c.cycle.darts.toFinset.card ≤ c.cycle.dropLast.support.toFinset.card := by
    calc
      _ ≤ c.cycle.darts.length := List.toFinset_card_le _
      _ = c.cycle.dropLast.support.length := by
        rw [Walk.length_darts,Walk.length_support,Walk.length_dropLast]
        have := c.isCycle.three_le_length; omega
      _ = c.cycle.dropLast.support.toFinset.card := (List.toFinset_card_of_nodup c.isCycle.isPath_dropLast.support_nodup).symm
  omega

lemma vertices_card : c.vertices.card ≤ 2 * Fintype.card c.W :=
  c.vertices_card_support.trans (Nat.mul_le_mul_left _ (Finset.card_le_univ _))

lemma mem_vertices (v : V) : v ∈ c.vertices ↔ ∃ d ∈ c.cycle.darts, v = (c.rep d).fst ∨ v = (c.rep d).snd := by
  simp [vertices]

theorem complete [DecidableEq V]
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z))
    (hs : ∀ z, (route z).IsPath)
    (ha : ∀ z, Disjoint (pathInterior (route z)) c.vertices)
    (hd : Pairwise fun z w => Disjoint (pathInterior (route z)) (pathInterior (route w))) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧
      p.edgeSet = c.edges ∪ ⋃ z, (route z).edgeSet := by
  classical
  let visits : ∀ z, G.Walk (c.start z) (c.finish z) := fun z =>
    if h : z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z then route ⟨z,h⟩
    else (Walk.nil : G.Walk (c.start z) (c.start z)).copy rfl (by
      by_cases hz : z ∈ c.cycle.dropLast.support
      · exact not_not.mp (fun hn => h ⟨hz,hn⟩)
      · exact c.outside z hz)
  have hv (z : c.Switch) : visits z = route z := by simp only [visits,dite_eq_left z.property]
  have hnil (z : c.W) (hz : ¬(z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z)) :
      (visits z).Nil := by simp only [visits,dite_eq_right hz,Walk.nil_copy,Walk.nil_nil]
  have hpath : ∀ z, (visits z).IsPath := by
    intro z
    by_cases hz : z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z
    · simpa only [visits,dite_eq_left hz] using hs ⟨z,hz⟩
    · simp [visits,dite_eq_right hz]
  have hinter (z : c.W) : visitInterior c.start c.finish visits z = (pathInterior (visits z):Set V) := by
    ext v; simp [visitInterior,pathInterior]
  have h_avoid : ∀ z ∈ c.cycle.dropLast.support, Disjoint
      (visitInterior c.start c.finish visits z) {v | ∃ d ∈ c.cycle.darts, v = (c.rep d).fst ∨ v = (c.rep d).snd} := by
    intro z hz
    rw [hinter]
    have he : {v | ∃ d ∈ c.cycle.darts, v = (c.rep d).fst ∨ v = (c.rep d).snd} = (c.vertices:Set V) := by
      ext v; exact (c.mem_vertices v).symm
    rw [he,Finset.disjoint_coe]
    by_cases hne : c.start z ≠ c.finish z
    · rw [hv ⟨z,hz,hne⟩]; exact ha _
    · have hn := hnil z (by tauto)
      simp [Finset.disjoint_left,pathInterior,Walk.nil_iff_support_eq.mp hn]
  have h_dis : Pairwise fun z w : {z // z ∈ c.cycle.dropLast.support} =>
      Disjoint (visitInterior c.start c.finish visits z) (visitInterior c.start c.finish visits w) := by
    intro z w hzw
    rw [hinter,hinter,Finset.disjoint_coe]
    by_cases hz : c.start z ≠ c.finish z
    · by_cases hw : c.start w ≠ c.finish w
      · rw [hv ⟨z,z.property,hz⟩,hv ⟨w,w.property,hw⟩]
        exact hd (fun h => hzw (Subtype.ext (congrArg (fun t : c.Switch => (t:c.W)) h)))
      · have hn := hnil w (by tauto); simp [Finset.disjoint_left,pathInterior,Walk.nil_iff_support_eq.mp hn] ; tauto
    · have hn := hnil z (by tauto); simp [Finset.disjoint_left,pathInterior,Walk.nil_iff_support_eq.mp hn]
  obtain ⟨v,p,hp,hedge⟩ := inflate_represented_cycle c.rep c.start c.finish c.cycle c.isCycle c.ports visits
    (fun z _ => hpath z) (switch_supports_separated {z | z ∈ c.cycle.dropLast.support}
      c.project c.start c.finish visits c.projects
      (by
        intro z hz
        rw [cyclePortSet_eq_representative_vertices c.rep c.start c.finish c.cycle c.isCycle c.ports]
        exact h_avoid z hz)
      (fun z hz w hw hzw => h_dis (show (⟨z,hz⟩:{z // z ∈ c.cycle.dropLast.support}) ≠ ⟨w,hw⟩ from
        fun h => hzw (congrArg Subtype.val h))))
  refine ⟨v,p,hp,hedge.trans ?_⟩
  congr 1
  ext e
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨z,hz,he⟩
    by_cases hne : c.start z ≠ c.finish z
    · exact ⟨⟨z,hz,hne⟩,by rwa [hv ⟨z,hz,hne⟩] at he⟩
    · have hn := hnil z (by tauto)
      have hh := he
      simp [Walk.edgeSet,Walk.edges_eq_nil.mpr hn] at hh
  · rintro ⟨z,he⟩; exact ⟨z,z.property.1,by rwa [hv]⟩

end CycleOutline
end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

structure RoutingTemplate {V : Type} (G : SimpleGraph V) where
  Arity : Type
  finiteArity : Fintype Arity
  x : Arity → V
  y : Arity → V
  ne : ∀ i, x i ≠ y i
  edges : Set (Sym2 V)
  subset : edges ⊆ G.edgeSet
  vertices : Finset V
  incident : ∀ i v, x i = v ∨ y i = v → ∃ w, s(v,w) ∈ edges
  unique : ∀ i j v, (x i = v ∨ y i = v) → (x j = v ∨ y j = v) → i = j
  complete : ∀ q : ∀ i, G.Walk (x i) (y i),
    (∀ i, (q i).IsPath) →
    (∀ i, Disjoint (pathInterior (q i)) vertices) →
    Pairwise (fun i j => Disjoint (pathInterior (q i)) (pathInterior (q j))) →
    CycleOrSingleEdge G (edges ∪ ⋃ i, (q i).edgeSet)
attribute [instance] RoutingTemplate.finiteArity

namespace RoutingTemplate
variable {V : Type} {G : SimpleGraph V}

def ofCycle (c : CycleOutline G) : RoutingTemplate G where
  Arity := c.Switch
  finiteArity := inferInstance
  x := fun i => c.start i
  y := fun i => c.finish i
  ne := fun i => i.property.2
  edges := c.edges
  subset := c.edges_subset
  vertices := c.vertices
  incident := fun i v h => by obtain ⟨w,_,he⟩ := c.endpoint_incident i v h; exact ⟨w,he⟩
  unique := c.endpoint_unique
  complete := by
    intro q hs ha hd
    obtain ⟨v,p,hp,he⟩ := c.complete q hs ha hd
    exact Or.inl ⟨v,p,hp,he.symm⟩

def ofSingle (e : Sym2 V) (he : e ∈ G.edgeSet) : RoutingTemplate G where
  Arity := Empty
  finiteArity := inferInstance
  x := Empty.elim
  y := Empty.elim
  ne := fun i => i.elim
  edges := {e}
  subset := Set.singleton_subset_iff.mpr he
  vertices := ∅
  incident := fun i => i.elim
  unique := fun i => i.elim
  complete := by intro q _ _ _; exact Or.inr ⟨e,he,by simp⟩

def ofPath {x y : V} (p : G.Walk x y) (hp : p.IsPath) (hl : 2 ≤ p.length) : RoutingTemplate G where
  Arity := Unit
  finiteArity := inferInstance
  x := fun _ => y
  y := fun _ => x
  ne := fun _ he => by
    have hn : p.Nil := hp.nil_iff_eq.mpr he.symm
    have := Walk.length_eq_zero_iff.mpr hn
    omega
  edges := p.edgeSet
  subset := p.edges_subset_edgeSet
  vertices := p.support.toFinset
  incident := by
    intro i v hv
    have hn : ¬p.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
    rcases hv with rfl | rfl
    · obtain ⟨w,_,he⟩ := finish_has_incident_edge p hn; exact ⟨w,he⟩
    · obtain ⟨w,_,he⟩ := start_has_incident_edge p hn; exact ⟨w,he⟩
  unique := fun _ _ _ _ _ => Subsingleton.elim _ _
  complete := by
    intro q hs ha hd
    obtain ⟨hc,he⟩ := close_trimmed_path p (q ()) hp (hs ()) hl (by
      intro v hv hxa hxb hpv
      exact Finset.disjoint_left.mp (ha ())
        (by simp [pathInterior,hv,hxa,hxb]) (List.mem_toFinset.mpr hpv))
    refine Or.inl ⟨x,p.append (q ()),hc,?_⟩
    have hh : ∀ i : Unit, q i = q () := fun i => by cases i; rfl
    simp_rw [hh,Set.iUnion_const]
    exact he.symm

lemma ofCycle_arity_card (c : CycleOutline G) :
    Fintype.card (ofCycle c).Arity ≤ Fintype.card c.W := Fintype.card_subtype_le _

lemma ofPath_vertices_card [Fintype V] {x y : V} (p : G.Walk x y) (hp : p.IsPath) (hl : 2 ≤ p.length) :
    (ofPath p hp hl).vertices.card ≤ Fintype.card V := Finset.card_le_univ _

end RoutingTemplate

theorem uniform_resolve_templates :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V R B : Type) [Fintype V] [Fintype R] [Fintype B],
      ∀ (G F : SimpleGraph V) (P : R → SimpleGraph V) (U : R → Finset V),
      F ≤ G → (∀ r, P r ≤ G) →
      Pairwise (fun r s => Disjoint (P r).edgeSet (P s).edgeSet) →
      Pairwise (fun r s => Disjoint (U r) (U s)) →
      (∀ r, Disjoint F.edgeSet (P r).edgeSet) →
      (∀ r, CutExpansionOn (P r) (U r) (D^(9/10:ℝ)/4)) →
      (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
      ∀ (b : B → RoutingTemplate G),
      (∀ j, (b j).edges ⊆ F.edgeSet) →
      Pairwise (fun j k => Disjoint (b j).edges (b k).edges) →
      ∀ owner : (j : B) → (b j).Arity → R,
      (∀ j i, (b j).x i ∈ U (owner j i) ∧ (b j).y i ∈ U (owner j i)) →
      (∀ j i, (F.degree ((b j).x i):ℝ) ≤ D^(1/100:ℝ) ∧
        (F.degree ((b j).y i):ℝ) ≤ D^(1/100:ℝ)) →
      (∀ j, (Fintype.card (b j).Arity:ℝ) ≤ D^(3/10:ℝ)) →
      (∀ j, ((b j).vertices.card:ℝ) ≤ 2*D^(3/10:ℝ)) →
      ∃ (parts : B → Set (Sym2 V)) (used : Set (Sym2 V)),
        (∀ j, CycleOrSingleEdge G (parts j)) ∧
        Pairwise (fun j k => Disjoint (parts j) (parts k)) ∧
        used ⊆ ⋃ r, (P r).edgeSet ∧ Disjoint F.edgeSet used ∧
        (⋃ j, parts j) = (⋃ j, (b j).edges) ∪ used := by
  classical
  obtain ⟨D₀,hD₀,hr⟩ := uniform_multi_batch_routing
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V R B _ _ _ G F P U hFG hPG hPP hUU hFP he hsize b hsub hdis owner hends hdeg hnum hvertices
  let I := Σ j, (b j).Arity
  let x : I → V := fun i => (b i.1).x i.2
  let y : I → V := fun i => (b i.1).y i.2
  have hl (v : V) : (endpointLoad univ x y v:ℝ) ≤ D^(1/100:ℝ) := by
    have hload : endpointLoad univ x y v ≤ F.degree v := by
      have hh := demand_load_le_degree F (fun j => (b j).edges) hdis
        Sigma.fst x y (by
          rintro ⟨j,i⟩ ⟨k,l⟩ v h h₁ h₂
          dsimp only at h; subst k
          congr 1; exact (b j).unique i l v h₁ h₂) (by
          rintro ⟨j,i⟩ v h
          obtain ⟨w,hw⟩ := (b j).incident i v h
          exact ⟨w,hsub j hw,hw⟩) v
      simpa [demandLoad,endpointLoad] using hh
    by_cases hz : endpointLoad univ x y v = 0
    · rw [hz,Nat.cast_zero]; exact Real.rpow_nonneg (by linarith) _
    · have hp : 0 < (univ.filter fun i => x i = v ∨ y i = v).card := by
        change 0 < endpointLoad univ x y v; omega
      obtain ⟨⟨j,i⟩,hi⟩ := Finset.card_pos.mp hp
      have hv : (b j).x i = v ∨ (b j).y i = v := (Finset.mem_filter.mp hi).2
      have hh : (F.degree v:ℝ) ≤ D^(1/100:ℝ) := by
        rcases hv with rfl | rfl
        · exact (hdeg j i).1
        · exact (hdeg j i).2
      exact (Nat.cast_le.mpr hload).trans hh
  have hteam (i : I) : ((univ.filter fun j : I => j.1 = i.1).card:ℝ) ≤ D^(3/10:ℝ) := by
    have hc : (univ.filter fun j : I => j.1 = i.1).card = Fintype.card (b i.1).Arity := by
      rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sigma]
      calc
        _ = ∑ j : B, if j = i.1 then Fintype.card (b j).Arity else 0 := by
          apply Finset.sum_congr rfl; intro j _
          by_cases hh : j = i.1 <;> simp [hh]
        _ = _ := by simp
    rw [hc]; exact hnum i.1
  obtain ⟨q,hq,hqd,hqi⟩ := hr D hD V R I B G P U hPG hPP hUU he hsize
    (fun i => owner i.1 i.2) x y (fun i => ⟨(hends i.1 i.2).1,(hends i.1 i.2).2,(b i.1).ne i.2⟩)
    Sigma.fst (fun i => (b i.1).vertices) hl hteam (fun i => hvertices i.1)
  let used := ⋃ i, (q i).edgeSet
  let parts := fun j => (b j).edges ∪ ⋃ i, (q ⟨j,i⟩).edgeSet
  have hu : used ⊆ ⋃ r, (P r).edgeSet := by
    apply Set.iUnion_subset; intro i
    exact Set.subset_iUnion_of_subset (owner i.1 i.2) (hq i).2.2.1
  have hFu : Disjoint F.edgeSet used := by
    refine Set.disjoint_iUnion_right.mpr (fun i => ?_)
    exact (hFP _).mono_right (hq i).2.2.1
  have hbu : ∀ j, Disjoint (b j).edges used := fun j => hFu.mono_left (hsub j)
  refine ⟨parts,used,?_,?_,hu,hFu,?_⟩
  · intro j
    exact (b j).complete (fun i => q ⟨j,i⟩) (fun i => (hq _).1) (fun i => (hq _).2.2.2)
      (fun i l hil => hqi _ _ (fun h => hil (eq_of_heq (Sigma.mk.inj_iff.mp h).2)) rfl)
  · intro j k hjk
    apply Set.disjoint_union_left.mpr; constructor
    · apply Set.disjoint_union_right.mpr; constructor
      · exact hdis hjk
      · exact (hbu j).mono_right (Set.iUnion_subset (fun i => Set.subset_iUnion (fun z : I => (q z).edgeSet) ⟨k,i⟩))
    · apply Set.disjoint_union_right.mpr; constructor
      · exact ((hbu k).mono_right (Set.iUnion_subset (fun i => Set.subset_iUnion (fun z : I => (q z).edgeSet) ⟨j,i⟩))).symm
      · apply Set.disjoint_iUnion_left.mpr; intro i
        apply Set.disjoint_iUnion_right.mpr; intro l
        exact hqd (fun h => hjk (congrArg Sigma.fst h))
  · ext e
    simp only [parts,used,Set.mem_iUnion,Set.mem_union]
    constructor
    · rintro ⟨j,he|⟨i,hi⟩⟩
      · exact Or.inl ⟨j,he⟩
      · exact Or.inr ⟨⟨j,i⟩,hi⟩
    · rintro (⟨j,he⟩|⟨⟨j,i⟩,he⟩)
      · exact ⟨j,Or.inl he⟩
      · exact ⟨j,Or.inr ⟨i,he⟩⟩

end
end ErdosGallai.Batch
end
end
end

end OAI
