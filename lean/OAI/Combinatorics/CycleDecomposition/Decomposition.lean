import OAI.Combinatorics.CycleDecomposition.EndpointPartition

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai

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
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

theorem small_residue (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G P : SimpleGraph V)
        [DecidableRel P.Adj], P ≤ G →
      D^(9/10:ℝ) ≤ (Fintype.card V:ℝ) →
      (Fintype.card V:ℝ) ≤ D^(51/50:ℝ) →
      Splitting.CutExpansion P (c*D^(9/10:ℝ)) →
      ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V))
        (W : Fin 3 → Finset V) (H : Fin 3 → SimpleGraph V),
        (∀ i, CycleOrSingleEdge G (parts i)) ∧
        Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
        (∀ b, H b ≤ G ∧ (H b).support ⊆ (W b : Set V)) ∧
        (∀ b, (W b).card < Fintype.card V) ∧
        ((∑ b, (W b).card : ℕ):ℝ) ≤ η * Fintype.card V ∧
        Pairwise (fun b d => Disjoint (H b).edgeSet (H d).edgeSet) ∧
        (∀ b i, Disjoint (H b).edgeSet (parts i)) ∧
        ((⋃ i, parts i) ∪ (⋃ b, (H b).edgeSet)) = G.edgeSet ∧
        k ≤ 9 * Fintype.card V := by
  classical
  have ha : 0 < reservoirExpansionCoefficient c := by
    unfold reservoirExpansionCoefficient
    exact div_pos (lt_min hc (by norm_num)) (by norm_num)
  have hp : 0 < reservoirProbability η := by
    unfold reservoirProbability
    exact lt_min (div_pos hη (by norm_num)) (by norm_num)
  obtain ⟨D₁,hprep⟩ := reservoir_preparation c η hc hη
  obtain ⟨D₂,hD₂,hclose⟩ := uniform_three_reservoir_completion
    (reservoirExpansionCoefficient c) (reservoirProbability η) ha hp
  refine ⟨max D₁ D₂, hD₂.trans_le (le_max_right _ _), ?_⟩
  intro D hD V _ _ G P _ hPG hlo hhi hexp
  obtain ⟨ω,W,r,hPG',hPP,hPexp,hWW,hW2,hWsize,hWlt,hWsum,hWexp,hr,hrne,hcap⟩ :=
    hprep D ((le_max_left _ _).trans hD) V G P hPG hlo hhi hexp
  let P' := fun b => Splitting.colorGraph P ω b
  have hWW' : Pairwise fun b d => Disjoint (W b : Set V) (W d : Set V) := by
    intro b d hbd
    exact Finset.disjoint_coe.mpr (hWW b d hbd)
  let R := fun b => reservoirInternal (P' b) (W b)
  let T := fun b => R b ∪ (reservoirSpokes (W b) (r b) : Set (Sym2 V))
  let E : Set (Sym2 V) := ⋃ b, T b
  have hres := reservoir_reservations G P' W r hPG' hPP
    (fun b v hv t => (hr b v hv t).2)
  have hE : E ⊆ G.edgeSet := Set.iUnion_subset fun b =>
    Set.union_subset (hres.1 b).1 (hres.1 b).2
  let K := fun b => complementaryReservoirGraph (G.deleteEdges E)
    (fun b => (W b : Set V)) hWW' b
  have hK := complementary_reservoir_graphs (G.deleteEdges E)
    (fun b => (W b : Set V)) hWW'
  have hKG : ∀ b, K b ≤ G := fun b => (hK.1 b).trans (G.deleteEdges_le E)
  have hledger := complementary_reservation_ledger G (fun b => (W b : Set V)) hWW' E hE
  have hKT : ∀ b d, Disjoint (K b).edgeSet (T d) := fun b d =>
    (hledger.2.1 b).mono_right (Set.subset_iUnion T d)
  have hx : ∀ b : Fin 3, EndpointPathPartition (K b) := fun b => endpoint_path_partition (K b)
  choose k Q hQQ hQc hQl hQn using hx
  let x := fun b i => (Q b i).start
  let y := fun b i => (Q b i).finish
  let q : ∀ b i, G.Walk (x b i) (y b i) := fun b i => (Q b i).walk.mapLe (hKG b)
  have hqp : ∀ b i, (q b i).IsPath := fun b i => (Q b i).isPath.mapLe _
  have hql : ∀ b i, 0 < (q b i).length := by
    intro b i
    simpa [q] using (Q b i).positive
  have hqo : ∀ b i v, v ∈ (q b i).support → v ∉ W b := by
    intro b i v hv
    apply complementary_walk_outside (fun b => (W b : Set V)) hWW' b
      (Q b i).walk (Q b i).positive v
    simpa [q] using hv
  have hqd : ∀ b, Pairwise fun i j => Disjoint (q b i).edgeSet (q b j).edgeSet := by
    intro b i j hij
    simpa [q] using hQQ b hij
  have hqc : ∀ b, (⋃ i, (q b i).edgeSet) = (K b).edgeSet := by
    intro b
    simpa [q] using hQc b
  obtain ⟨C,hCy,hCC,hCsub,hcover,hcount⟩ := hclose D ((le_max_right _ _).trans hD)
    V G P' K hPG' hPP W r hWexp hW2 hhi hr hrne hcap
    hledger.1 hKT (fun b => Fin (k b)) x y q hqp hql hqo hqd hqc
      (by
        intro b v
        dsimp only [endpointLoad,x,y]
        convert hQl b v using 2
        ext i
        simp)
  let I := Σ b, Fin (k b)
  let CE : I → Set (Sym2 V) := fun z => (C z.1 z.2).edgeSet
  have hCE : ∀ i, CE i ⊆ G.edgeSet := fun i => (C i.1 i.2).edges_subset_edgeSet
  have hEeq : E = (⋃ b, R b) ∪ (allReservoirSpokes W r : Set _) := by
    simp only [E,T,coe_allReservoirSpokes,Set.iUnion_union_distrib]
  have hcov : G.edgeSet \ ((⋃ b, R b) ∪ (allReservoirSpokes W r : Set _)) ⊆
      completedEdges CE := by
    rw [← hEeq, ← SimpleGraph.edgeSet_deleteEdges, ← hK.2.2.2]
    exact hcover
  obtain ⟨hsupp,hind,hHe,hHH,hHC,hHS,hCS,hu,hnum⟩ :=
    three_reservoir_remainder G P' W r hPG' hPP
      (fun b v hv t => (hr b v hv t).2) CE hCE hCC hcount hcov
  let H := residualInternalGraph G R CE
  let S := unusedSpokes (↑(allReservoirSpokes W r)) CE
  let J := I ⊕ S
  let parts : J → Set (Sym2 V) := Sum.elim CE (fun e => {e.val})
  have hSsub : (S : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    have hh : e ∈ (allReservoirSpokes W r : Set _) := by
      have hh := he
      simp only [Finset.mem_coe,S,unusedSpokes,Set.mem_toFinset,Set.mem_sdiff] at hh
      exact hh.1
    exact hE (by rw [hEeq]; exact Or.inr hh)
  have hpart : ∀ j, CycleOrSingleEdge G (parts j) := by
    intro j
    rcases j with i | e
    · exact Or.inl ⟨x i.1 i.2,C i.1 i.2,hCy i.1 i.2,rfl⟩
    · exact Or.inr ⟨e.val,hSsub e.property,rfl⟩
  have hpd : Pairwise fun i j => Disjoint (parts i) (parts j) := by
    intro i j hij
    rcases i with i | e <;> rcases j with j | f
    · exact hCC (fun h => hij (congrArg Sum.inl h))
    · exact (hCS i).mono_right (Set.singleton_subset_iff.mpr f.property)
    · exact (hCS j).symm.mono_left (Set.singleton_subset_iff.mpr e.property)
    · exact Set.disjoint_singleton.mpr (fun h => hij (congrArg Sum.inr (Subtype.ext h)))
  have hpartU : (⋃ j, parts j) = completedEdges CE ∪ (S : Set (Sym2 V)) := by
    ext e
    simp only [Set.mem_iUnion, Set.mem_union, completedEdges, parts]
    constructor
    · rintro ⟨i,hi⟩
      rcases i with i | f
      · exact Or.inl ⟨i,hi⟩
      · exact Or.inr ((Set.mem_singleton_iff.mp hi) ▸ f.property)
    · rintro (⟨i,hi⟩ | he)
      · exact ⟨Sum.inl i,hi⟩
      · exact ⟨Sum.inr ⟨e,he⟩,rfl⟩
  let equiv := Fintype.equivFin J
  refine ⟨Fintype.card J,fun i => parts (equiv.symm i),W,H,?_,?_,?_,hWlt,hWsum,
    hHH,?_,?_,?_⟩
  · exact fun i => hpart _
  · intro i j hij
    exact hpd (fun h => hij (equiv.symm.injective h))
  · intro b
    refine ⟨?_,hsupp b⟩
    exact edgeRestriction_le G _
  · intro b i
    rcases hji : equiv.symm i with j | e
    all_goals simp only [hji, parts, Sum.elim_inl, Sum.elim_inr]
    · exact hHC b j
    · exact (hHS b).mono_right (Set.singleton_subset_iff.mpr e.property)
  · have he : (⋃ i, parts (equiv.symm i)) = ⋃ j, parts j := by
      ext e
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨i,hi⟩ => ⟨equiv.symm i,hi⟩,
        fun ⟨j,hj⟩ => ⟨equiv j,by simpa using hj⟩⟩
    rw [he,hpartU]
    exact hu
  · simpa only [J,Fintype.card_sum,Fintype.card_coe] using hnum

end
end ErdosGallai

namespace ErdosGallai
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
end ErdosGallai
namespace ErdosGallai
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
end ErdosGallai
namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_adjoin_same {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hHP : ∀ j i, Disjoint (H j).edgeSet (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) := by
  let f : ∀ j, H j →g G := fun j => ⟨id,fun h => hHG j h⟩
  have he (j) : Sym2.map (f j) '' (H j).edgeSet = (H j).edgeSet := by
    have hf : (f j : V → V) = id := rfl
    rw [hf, Sym2.map_id, Set.image_id]
  apply decompositionCost_adjoin G parts hp hd (fun _ => V) H f (fun _ => Function.injective_id)
  · simpa only [he] using hHH
  · simpa only [he] using hHP
  · simpa only [he] using hu

lemma decompositionCost_assemble_same {V J : Type} [Fintype V] [Fintype J]
    (G : SimpleGraph V) (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hu : (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ ∑ j, decompositionCost (H j) := by
  simpa using decompositionCost_adjoin_same (I := Empty) G Empty.elim (fun i => nomatch i)
    (by intro i; exact i.elim) H hHG hHH (fun _ i => nomatch i) (by simpa using hu)

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem uniform_piece_cost (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ (n : ℕ) (C : ℝ), 0 ≤ C →
      (∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < n →
        (decompositionCost H:ℝ) ≤ C * Fintype.card W) →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G P : SimpleGraph V)
        [DecidableRel P.Adj], P ≤ G → Fintype.card V ≤ n →
      D^(9/10:ℝ) ≤ (Fintype.card V:ℝ) →
      (Fintype.card V:ℝ) ≤ D^(51/50:ℝ) →
      Splitting.CutExpansion P (c*D^(9/10:ℝ)) →
      (decompositionCost G:ℝ) ≤ (9+C*η)*Fintype.card V := by
  obtain ⟨D₀,hD₀,hres⟩ := small_residue c η hc hη
  refine ⟨D₀,hD₀,?_⟩
  intro D hD n C hC ih V _ _ G P _ hPG hn hlo hhi he
  obtain ⟨k,parts,W,H,hp,hd,hHG,hWlt,hWsum,hHH,hHP,hu,hk⟩ :=
    hres D hD V G P hPG hlo hhi he
  have hcost (b : Fin 3) : (decompositionCost (H b):ℝ) ≤ C * (W b).card := by
    have hA : ∀ ⦃x y⦄, (H b).Adj x y → x ∈ W b ∧ y ∈ W b := by
      intro x y hxy
      exact ⟨(hHG b).2 ⟨y,hxy⟩,(hHG b).2 ⟨x,hxy.symm⟩⟩
    calc
      _ ≤ (decompositionCost ((H b).induce (W b:Set V)):ℝ) :=
        Nat.cast_le.mpr (decompositionCost_on _ _ hA)
      _ ≤ C * Fintype.card (W b:Set V) := ih _ _ (by simpa using (hWlt b).trans_le hn)
      _ = _ := by simp
  have htot := decompositionCost_adjoin_same G parts hp hd H (fun b => (hHG b).1) hHH hHP hu
  have hsum : (∑ b, (decompositionCost (H b):ℝ)) ≤ C * ∑ b, ((W b).card:ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => hcost b)
  have hsum' := mul_le_mul_of_nonneg_left hWsum hC
  have hk' : (k:ℝ) ≤ 9 * Fintype.card V := by exact_mod_cast hk
  have htot' : (decompositionCost G:ℝ) ≤ k + ∑ b, (decompositionCost (H b):ℝ) := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_sum] using (Nat.cast_le.mpr htot : (decompositionCost G:ℝ) ≤ _)
  push_cast at hsum'
  nlinarith

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem uniform_piece_cost_on (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ (n : ℕ) (C : ℝ), 0 ≤ C →
      (∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < n →
        (decompositionCost H:ℝ) ≤ C * Fintype.card W) →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G P : SimpleGraph V)
        [DecidableRel P.Adj] (A : Finset V), P ≤ G → A.card ≤ n →
      (∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A) →
      D^(9/10:ℝ) ≤ (A.card:ℝ) → (A.card:ℝ) ≤ D^(51/50:ℝ) →
      CutExpansionOn P A (c*D^(9/10:ℝ)) →
      (decompositionCost G:ℝ) ≤ (9+C*η)*A.card := by
  obtain ⟨D₀,hD₀,hcost⟩ := uniform_piece_cost c η hc hη
  refine ⟨D₀,hD₀,?_⟩
  intro D hD n C hC ih V _ _ G P _ A hPG hn hA hlo hhi he
  have hcost' := hcost D hD n C hC ih (A:Set V) (G.induce (A:Set V))
    (P.induce (A:Set V)) (fun _ _ h => hPG h) (by simpa using hn)
    (by simpa using hlo) (by simpa using hhi) (cutExpansion_induce P A _ he)
  calc
    _ ≤ (decompositionCost (G.induce (A:Set V)):ℝ) := Nat.cast_le.mpr (decompositionCost_on G A hA)
    _ ≤ _ := by simpa using hcost'

end
end ErdosGallai

end
end
end

end OAI
