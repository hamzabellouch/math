import OAI.Combinatorics.CycleDecomposition.ScaleHierarchy

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def graphUnion (L : List (SimpleGraph V)) : SimpleGraph V := L.foldr (· ⊔ ·) ⊥

@[simp] lemma graphUnion_nil {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] : graphUnion ([] : List (SimpleGraph V)) = ⊥ := rfl
@[simp] lemma graphUnion_cons {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (L) : graphUnion (G::L) = G ⊔ graphUnion L := rfl
lemma graphUnion_adj {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (SimpleGraph V)) (x y : V) :
    (graphUnion L).Adj x y ↔ ∃ G ∈ L, G.Adj x y := by
  induction L with
  | nil => simp
  | cons G L ih => simp only [graphUnion_cons,SimpleGraph.sup_adj,ih,List.mem_cons]; aesop

lemma edgeOccurrences_pos (L : List (SimpleGraph V)) (x y : V) :
    0 < edgeOccurrences L x y ↔ (graphUnion L).Adj x y := by
  simp [edgeOccurrences,List.countP_pos_iff,graphUnion_adj]

lemma graphPartition_union {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : graphUnion L = G := by
  ext x y
  rw [← edgeOccurrences_pos,h x y]
  split_ifs <;> simp_all

lemma graphPartition_of_le_one (L : List (SimpleGraph V))
    (h : ∀ x y, edgeOccurrences L x y ≤ 1) : GraphPartition (graphUnion L) L := by
  intro x y
  have hh := h x y
  rw [← edgeOccurrences_pos]
  split_ifs <;> omega

lemma edgeOccurrences_sublist {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {L M : List (SimpleGraph V)} (h : L.Sublist M) (x y : V) :
    edgeOccurrences L x y ≤ edgeOccurrences M x y := by
  exact List.Sublist.countP_le h

lemma graphPartition_sublist {G : SimpleGraph V} {L M : List (SimpleGraph V)}
    (hp : GraphPartition G M) (h : L.Sublist M) : GraphPartition (graphUnion L) L := by
  apply graphPartition_of_le_one
  intro x y
  have hh := edgeOccurrences_sublist h x y
  rw [hp x y] at hh
  split_ifs at hh <;> omega

lemma graphUnion_sublist {L M : List (SimpleGraph V)} (h : L.Sublist M) : graphUnion L ≤ graphUnion M := by
  intro x y hxy
  obtain ⟨G,hG,hxy⟩ := (graphUnion_adj _ _ _).mp hxy
  exact (graphUnion_adj _ _ _).mpr ⟨G,h.subset hG,hxy⟩

lemma graphUnion_append (L M : List (SimpleGraph V)) : graphUnion (L++M) = graphUnion L ⊔ graphUnion M := by
  ext x y
  simp only [graphUnion_adj,List.mem_append,SimpleGraph.sup_adj]
  aesop

lemma edgeOccurrences_perm {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {L M : List (SimpleGraph V)} (h : L.Perm M) (x y : V) :
    edgeOccurrences L x y = edgeOccurrences M x y := List.Perm.countP_eq _ h

lemma graphPartition_perm {G : SimpleGraph V} {L M : List (SimpleGraph V)}
    (h : GraphPartition G L) (hp : L.Perm M) : GraphPartition G M := by
  intro x y
  rw [← edgeOccurrences_perm hp]
  exact h x y

lemma graphUnion_supported (L : List (AssignedPiece V)) (A : Finset V)
    (h : ∀ P ∈ L, P.vertices ⊆ A) : SupportedOn (graphUnion (L.map AssignedPiece.graph)) A := by
  intro x y hxy
  obtain ⟨G,hG,hxy⟩ := (graphUnion_adj _ _ _).mp hxy
  obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hG
  exact ⟨h P hP (P.supported hxy).1,h P hP (P.supported hxy).2⟩

lemma edgeCount_union_le (L : List (SimpleGraph V)) :
    edgeCount (graphUnion L) ≤ (L.map edgeCount).sum := by
  induction L with
  | nil => simp
  | cons G L ih =>
    simp only [graphUnion_cons,List.map_cons,List.sum_cons]
    exact (edgeCount_sup_le G (graphUnion L)).trans (Nat.add_le_add_left ih _)

def levelCycles (s : SplitSystem V) (j : ℕ) (L : List (AssignedPiece V)) : List (SimpleGraph V) :=
  L.flatMap fun P => (s j P).cycles

def levelPieces (s : SplitSystem V) (j : ℕ) (L : List (AssignedPiece V)) : List (AssignedPiece V) :=
  L.flatMap fun P => (s j P).boxes.flatMap (s j P).pieces

lemma StageSplit.ledger {P : AssignedPiece V} (s : StageSplit P) (x y : V) :
    edgeOccurrences (s.cycles ++ (s.boxes.flatMap s.pieces).map AssignedPiece.graph ++
      s.children.map AssignedPiece.graph) x y = if P.graph.Adj x y then 1 else 0 := by
  have h := s.partition x y
  rw [edgeOccurrences_append] at h
  rw [← edgeOccurrences_refine s.boxes AssignedPiece.graph
    (fun B => s.remainder B :: (s.pieces B).map AssignedPiece.graph) s.box_partition] at h
  have he : edgeOccurrences (s.boxes.flatMap (fun B => s.remainder B ::
      (s.pieces B).map AssignedPiece.graph)) x y =
      edgeOccurrences ((s.boxes.flatMap s.pieces).map AssignedPiece.graph) x y +
      edgeOccurrences (s.children.map AssignedPiece.graph) x y := by
    rw [s.children_map (fun _ G => G)]
    induction s.boxes with
    | nil => simp
    | cons B L ih =>
      simp only [List.flatMap_cons,List.map_append,List.map_cons,edgeOccurrences_append,
        edgeOccurrences_cons] at *
      omega
  rw [he] at h
  simpa only [edgeOccurrences_append,Nat.add_assoc] using h

lemma level_ledger (s : SplitSystem V) (j) (L : List (AssignedPiece V)) (x y : V) :
    edgeOccurrences (levelCycles s j L ++ (levelPieces s j L).map AssignedPiece.graph ++
      (nextLayer s j L).map AssignedPiece.graph) x y = edgeOccurrences (L.map AssignedPiece.graph) x y := by
  induction L with
  | nil => simp [levelCycles,levelPieces,nextLayer]
  | cons P L ih =>
    have hp := (s j P).ledger x y
    simp only [levelCycles,levelPieces,nextLayer,List.flatMap_cons,List.map_append,
      List.map_cons,edgeOccurrences_append,edgeOccurrences_cons] at ih hp ⊢
    omega

def pastCycles (s : SplitSystem V) (j : ℕ) : ℕ → List (AssignedPiece V) → List (SimpleGraph V)
  | 0,_ => []
  | k+1,L => pastCycles s j k L ++ levelCycles s (j+k) (advance s j k L)

def pastPieces (s : SplitSystem V) (j : ℕ) : ℕ → List (AssignedPiece V) → List (AssignedPiece V)
  | 0,_ => []
  | k+1,L => pastPieces s j k L ++ levelPieces s (j+k) (advance s j k L)

lemma past_ledger (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) (x y : V) :
    edgeOccurrences (pastCycles s j k L ++ (pastPieces s j k L).map AssignedPiece.graph ++
      (advance s j k L).map AssignedPiece.graph) x y = edgeOccurrences (L.map AssignedPiece.graph) x y := by
  induction k with
  | zero => simp [pastCycles,pastPieces]
  | succ k ih =>
    have h := level_ledger s (j+k) (advance s j k L) x y
    simp only [pastCycles,pastPieces,advance_succ,List.map_append,edgeOccurrences_append] at ih h ⊢
    omega

lemma past_partition (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    GraphPartition P.graph (pastCycles s j k [P] ++ (pastPieces s j k [P]).map AssignedPiece.graph ++
      (advance s j k [P]).map AssignedPiece.graph) := by
  intro x y
  rw [past_ledger]
  simp

lemma levelCycles_good (s : SplitSystem V) (j) (L : List (AssignedPiece V)) :
    ∀ G ∈ levelCycles s j L, IsCycleGraph G := by
  intro G hG
  obtain ⟨P,_,hG⟩ := List.mem_flatMap.mp hG
  exact (s j P).cycles_good G hG

lemma pastCycles_good (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    ∀ G ∈ pastCycles s j k L, IsCycleGraph G := by
  induction k with
  | zero => simp [pastCycles]
  | succ k ih =>
    intro G hG
    rcases List.mem_append.mp hG with h | h
    · exact ih G h
    · exact levelCycles_good s (j+k) _ G h

lemma levelPieces_subset (s : SplitSystem V) (j) (L : List (AssignedPiece V)) (A : Finset V)
    (hL : ∀ P ∈ L, P.vertices ⊆ A) : ∀ Q ∈ levelPieces s j L, Q.vertices ⊆ A := by
  intro Q hQ
  obtain ⟨P,hP,B,hB,hQ⟩ := (by simpa [levelPieces,List.mem_flatMap] using hQ :
    ∃ P ∈ L, ∃ B ∈ (s j P).boxes, Q ∈ (s j P).pieces B)
  exact ((s j P).piece_subset B hB Q hQ).trans (((s j P).box_subset B hB).trans (hL P hP))

lemma levelPieces_mass (s : SplitSystem V) (j) (L : List (AssignedPiece V)) :
    vertexMass (levelPieces s j L) ≤ vertexMass (nextLayer s j L) := by
  induction L with
  | nil => simp [levelPieces,nextLayer]
  | cons P L ih =>
    have hs : vertexMass ((s j P).boxes.flatMap (s j P).pieces) ≤ vertexMass (s j P).boxes := by
      rw [vertexMass_flatMap]
      unfold vertexMass
      exact List.sum_le_sum (fun B hB => (s j P).pieces_mass hB)
    simp only [levelPieces,nextLayer,List.flatMap_cons,vertexMass_append,
      StageSplit.children_mass] at ih ⊢
    linarith

lemma levelCycles_length (s : SplitSystem V) (j) (L : List (AssignedPiece V)) (D : ℝ)
    (hb : ∀ P ∈ L, (s j P).Bounded D) :
    ((levelCycles s j L).length:ℝ) ≤ vertexMass L / (2*D^(1/100:ℝ)) := by
  induction L with
  | nil => simp [levelCycles]
  | cons P L ih =>
    have hp := (hb P (by simp)).1
    have hl := ih (fun Q hQ => hb Q (by simp [hQ]))
    simp only [levelCycles,List.flatMap_cons,List.length_append,Nat.cast_add,vertexMass_cons]
    rw [add_div]
    exact add_le_add hp hl

lemma pastPieces_mass (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    vertexMass (pastPieces s j k L) = ∑ l ∈ Finset.range k,
      vertexMass (levelPieces s (j+l) (advance s j l L)) := by
  induction k with
  | zero => simp [pastPieces]
  | succ k ih => simp [pastPieces,ih,Finset.sum_range_succ]

lemma pastCycles_length (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    ((pastCycles s j k L).length:ℝ) = ∑ l ∈ Finset.range k,
      ((levelCycles s (j+l) (advance s j l L)).length:ℝ) := by
  induction k with
  | zero => simp [pastCycles]
  | succ k ih => simp [pastCycles,ih,Finset.sum_range_succ]

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale

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
end ErdosGallai.Scale

namespace ErdosGallai.Scale
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
end ErdosGallai.Scale
namespace ErdosGallai.Scale
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
end ErdosGallai.Scale
namespace ErdosGallai.Scale
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
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma list_pairwise_get {A : Type cycleUniverse1} {R : A → A → Prop} {L : List A}
    (h : L.Pairwise R) (hs : (∀ ⦃left right⦄, R left right → R right left)) : Pairwise fun i j : Fin L.length => R (L.get i) (L.get j) := by
  intro i j hij
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun he => hij (Fin.ext he)) with hlt | hgt
  · exact List.pairwise_iff_getElem.mp h i.val j.val i.isLt j.isLt hlt
  · exact hs (List.pairwise_iff_getElem.mp h j.val i.val j.isLt i.isLt hgt)

lemma list_sum_get {A : Type cycleUniverse2} {M : Type cycleUniverse3} [AddCommMonoid M] (L : List A) (f : A → M) :
    (∑ i : Fin L.length, f (L.get i)) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  calc
    _ = (List.map f (List.ofFn L.get)).sum := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [List.ofFn_get]

lemma graphPartition_pairwise {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : L.Pairwise fun H K => Disjoint H.edgeSet K.edgeSet := by
  induction L generalizing G with
  | nil => simp
  | cons H L ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih (graphPartition_sublist h (List.sublist_cons_self _ _))⟩
    intro K hK
    apply Set.disjoint_left.mpr
    intro e he he'
    induction e using Sym2.ind with
    | _ x y =>
      have hc := h x y
      have hp : 0 < edgeOccurrences L x y := by
        rw [edgeOccurrences_pos,graphUnion_adj]
        exact ⟨K,hK,he'⟩
      have hxy : H.Adj x y := he
      simp only [edgeOccurrences_cons,hxy,ite_true] at hc
      split_ifs at hc <;> omega

lemma graphUnion_edges (L : List (SimpleGraph V)) :
    (⋃ i : Fin L.length, (L.get i).edgeSet) = (graphUnion L).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Set.mem_iUnion,SimpleGraph.mem_edgeSet]

    rw [graphUnion_adj]
    constructor
    · rintro ⟨i,h⟩; exact ⟨_,L.get_mem i,h⟩
    · rintro ⟨H,hH,h⟩
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
      exact ⟨i,h⟩

lemma decompositionCost_partition {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : decompositionCost G ≤ (L.map decompositionCost).sum := by
  rw [← list_sum_get L decompositionCost]
  apply decompositionCost_assemble_same G (fun i : Fin L.length => L.get i)
  · intro i; exact partition_member_le h (L.get_mem i)
  · exact list_pairwise_get (graphPartition_pairwise h) (fun _ _ h => h.symm)
  · rw [graphUnion_edges,graphPartition_union h]

lemma decompositionCost_cycle {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} (h : IsCycleGraph G) :
    decompositionCost G ≤ 1 := by
  apply decompositionCost_le
  have hp : CycleOrSingleEdge G G.edgeSet := by
    obtain ⟨a,p,hp,he⟩ := h
    exact Or.inl ⟨a,p,hp,he⟩
  refine ⟨fun _ => G.edgeSet,fun _ => hp,?_,?_⟩
  · intro i j hij; exact False.elim (hij (Subsingleton.elim i j))
  · ext e
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨(0 : Fin 1),h⟩⟩

lemma decompositionCost_edgeCount {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) : decompositionCost G ≤ edgeCount G := by
  have h := decompositionCost_singleEdges G
  rw [Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet] at h
  exact h

lemma decompositionCost_bot : decompositionCost (⊥ : SimpleGraph V) = 0 := by
  have h := decompositionCost_edgeCount (⊥ : SimpleGraph V)
  simp only [edgeCount_bot] at h
  omega

lemma decompositionCost_partition_real {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : (decompositionCost G:ℝ) ≤
      (L.map (fun H => (decompositionCost H:ℝ))).sum := by
  have hh : (decompositionCost G:ℝ) ≤ ((L.map decompositionCost).sum:ℕ) :=
    Nat.cast_le.mpr (decompositionCost_partition h)
  simpa [List.map_map,Function.comp_def] using hh

lemma decompositionCost_cycles (L : List (SimpleGraph V))
    (h : ∀ G ∈ L, IsCycleGraph G) :
    (L.map (fun H => (decompositionCost H:ℝ))).sum ≤ L.length := by
  calc
    _ ≤ (L.map (fun _ => (1:ℝ))).sum := List.sum_le_sum (fun G hG => by exact_mod_cast decompositionCost_cycle (h G hG))
    _ = _ := by simp

lemma partition_recombine {G : SimpleGraph V} {L M : List (SimpleGraph V)}
    (h : GraphPartition G (L++M)) : GraphPartition G (L++[graphUnion M]) := by
  have hm := graphPartition_sublist h (List.sublist_append_right L M)
  intro x y
  have hh := h x y
  simp only [edgeOccurrences_append] at hh ⊢
  rw [hm x y] at hh
  simpa using hh

lemma cost_recombine {G : SimpleGraph V} {L M : List (SimpleGraph V)}
    (h : GraphPartition G (L++M)) :
    (decompositionCost G:ℝ) ≤ (L.map (fun H => (decompositionCost H:ℝ))).sum +
      decompositionCost (graphUnion M) := by
  simpa using decompositionCost_partition_real (partition_recombine h)

lemma graphUnion_le_of_members {L : List (SimpleGraph V)} {G : SimpleGraph V}
    (h : ∀ H ∈ L, H ≤ G) : graphUnion L ≤ G := by
  intro x y hxy
  obtain ⟨H,hH,hxy⟩ := (graphUnion_adj _ _ _).mp hxy
  exact h H hH hxy

lemma graphPartition_of_pairwise (L : List (SimpleGraph V))
    (hd : L.Pairwise fun H K => Disjoint H.edgeSet K.edgeSet) : GraphPartition (graphUnion L) L := by
  induction L with
  | nil => intro x y; simp
  | cons G L ih =>
    obtain ⟨hG,hd⟩ := List.pairwise_cons.mp hd
    intro x y
    have hi := ih hd x y
    have hdis : ¬ (G.Adj x y ∧ (graphUnion L).Adj x y) := by
      rintro ⟨hg,hL⟩
      obtain ⟨H,hH,hxy⟩ := (graphUnion_adj _ _ _).mp hL
      exact Set.disjoint_left.mp (hG H hH) (show s(x,y) ∈ G.edgeSet from hg) hxy
    simp only [edgeOccurrences_cons,hi,graphUnion_cons,SimpleGraph.sup_adj]
    by_cases hg : G.Adj x y <;> by_cases hl : (graphUnion L).Adj x y <;> simp_all

end
end ErdosGallai.Scale

end
end
end

end OAI
