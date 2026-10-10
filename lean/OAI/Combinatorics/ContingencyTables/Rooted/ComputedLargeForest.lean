import OAI.Combinatorics.ContingencyTables.Rooted.ForestGreedySemantics
import OAI.Combinatorics.ContingencyTables.Rooted.ForestCapacity

namespace OAI

/-! # The executed maximum-capacity forest on the original cell vertices

The program uses the concrete row-then-column natural indexing. The
returned adjacency list is decoded and transported back to the original
bipartite vertex type. Its catalog and optimality obligations follow
from the stored capacities, rather than supplied correctness predicates.
-/

namespace ContingencyTables.ComputedLargeForest

open SimpleGraph MaximumForest ForestCapacity ForestGreedySemantics
open FiniteGraphRootProgram LargeEdgeCatalogProgram
open scoped BigOperators Classical

variable {m n : ℕ}

abbrev vertexEquiv : (Fin m⊕Fin n) ≃ Fin (m+n) := finSumFinEquiv

def small (b : Fin m→Fin n→ℕ) (W : ℕ) (i : Fin m) (j : Fin n) : Bool :=
  decide (b i j<W)

def graph (b : Fin m→Fin n→ℕ) (W : ℕ) : SimpleGraph (Fin (m+n)) :=
  (cellGraph (small b W)).map vertexEquiv.toEmbedding

def capacities (b : Fin m→Fin n→ℕ) (e : Sym2 (Fin (m+n))) : ℕ :=
  capacity b (Sym2.map vertexEquiv.symm e)

lemma graph_edge (b : Fin m→Fin n→ℕ) (W : ℕ) (i : Fin m) (j : Fin n) :
    (graph b W).Adj (vertexEquiv (.inl i)) (vertexEquiv (.inr j)) ↔ W≤b i j := by
  change ((cellGraph (small b W)).map vertexEquiv.toEmbedding).Adj
    (vertexEquiv.toEmbedding (.inl i)) (vertexEquiv.toEmbedding (.inr j)) ↔ _
  have hm := SimpleGraph.map_adj_apply (G:=cellGraph (small b W))
    (f:=vertexEquiv.toEmbedding) (a:=Sum.inl i) (b:=Sum.inr j)
  exact hm.trans (by simp only [cellGraph,cellAdj,small,decide_eq_false_iff_not,not_lt])

lemma capacities_cell (b : Fin m→Fin n→ℕ) (i : Fin m) (j : Fin n) :
    capacities b s(vertexEquiv (.inl i),vertexEquiv (.inr j))=b i j := by
  simp only [capacities,Sym2.map_mk,Equiv.symm_apply_apply,capacity_cell]

lemma catalog_correct (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (W : ℕ) :
    Catalog (graph b W) (capacities b) (catalog (NetworkVertexCode.data r c b,W)) := by
  constructor
  · intro e he
    obtain ⟨i,j,hb,rfl⟩ := (mem_catalog_code r c b W e).mp he
    refine ⟨vertexEquiv (.inl i),vertexEquiv (.inr j),(graph_edge b W i j).mpr hb,?_⟩
    rw [capacities_cell]
    simp only [vertexEquiv,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.val_castAdd,Fin.val_natAdd]
  · intro u v huv
    obtain ⟨a,rfl⟩ := vertexEquiv.surjective u
    obtain ⟨d,rfl⟩ := vertexEquiv.surjective v
    have hm := SimpleGraph.map_adj_apply (G:=cellGraph (small b W))
      (f:=vertexEquiv.toEmbedding) (a:=a) (b:=d)
    have h : (cellGraph (small b W)).Adj a d := hm.mp huv
    cases a with
    | inl i=>
      cases d with
      | inl k=>exact False.elim h
      | inr j=>
        left
        have hb : W≤b i j := by simpa only [cellGraph,cellAdj,small,
          decide_eq_false_iff_not,not_lt] using h
        apply (mem_catalog_code r c b W _).mpr
        refine ⟨i,j,hb,?_⟩
        rw [capacities_cell]
        simp only [vertexEquiv,finSumFinEquiv_apply_left,
          finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd]
    | inr j=>
      cases d with
      | inr k=>exact False.elim h
      | inl i=>
        right
        have hb : W≤b i j := by simpa only [cellGraph,cellAdj,small,
          decide_eq_false_iff_not,not_lt] using h
        apply (mem_catalog_code r c b W _).mpr
        refine ⟨i,j,hb,?_⟩
        rw [show s(vertexEquiv (.inr j),vertexEquiv (.inl i))=
          s(vertexEquiv (.inl i),vertexEquiv (.inr j)) from Sym2.eq_swap]
        rw [capacities_cell]
        simp only [vertexEquiv,finSumFinEquiv_apply_left,
          finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd]

lemma capacity_positive (b : Fin m→Fin n→ℕ) (W : ℕ) (hW : 1≤W) :
    ∀ e∈(graph b W).edgeSet,0<capacities b e := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v=>
    obtain ⟨a,rfl⟩ := vertexEquiv.surjective u
    obtain ⟨d,rfl⟩ := vertexEquiv.surjective v
    have hm := SimpleGraph.map_adj_apply (G:=cellGraph (small b W))
      (f:=vertexEquiv.toEmbedding) (a:=a) (b:=d)
    have h : (cellGraph (small b W)).Adj a d := hm.mp he
    cases a with
    | inl i=>
      cases d with
      | inl k=>exact False.elim h
      | inr j=>
        have hb : W≤b i j := by simpa only [cellGraph,cellAdj,small,
          decide_eq_false_iff_not,not_lt] using h
        rw [capacities_cell b i j]
        omega
    | inr j=>
      cases d with
      | inr k=>exact False.elim h
      | inl i=>
        rw [show s(vertexEquiv (.inr j),vertexEquiv (.inl i))=
          s(vertexEquiv (.inl i),vertexEquiv (.inr j)) from Sym2.eq_swap]
        have hb : W≤b i j := by simpa only [cellGraph,cellAdj,small,
          decide_eq_false_iff_not,not_lt] using h
        rw [capacities_cell b i j]
        omega

lemma empty_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (W : ℕ) :
    ForestGreedyProgram.emptyGraph (NetworkVertexCode.data r c b,W)=
      graphCode (⊥ : SimpleGraph (Fin (m+n))) := by
  simp only [ForestGreedyProgram.emptyGraph,vertexCount_code,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn,graphCode]
  apply congrArg List.ofFn
  funext v
  simp [adjacencyRow]

/-- The output list itself determines the forest. -/
noncomputable def computed (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (W : ℕ) :
    SimpleGraph (Fin m⊕Fin n) :=
  (decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W))).comap vertexEquiv

private lemma weight_transport {V U : Type*} [Fintype V] [Fintype U]
    (e : V≃U) (G : SimpleGraph V) (b : Sym2 V→ℕ) :
    weight (G.map e.toEmbedding) (fun a=>b (Sym2.map e.symm a))=weight G b := by
  rw [weight_eq,weight_eq,edgeFinset_map,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a _
  change b (Sym2.map e.symm (Sym2.map e a))=b a
  congr 1
  induction a using Sym2.inductionOn with
  | _ u v=>simp only [Sym2.map_mk,Equiv.symm_apply_apply]

/-- The executed list program gives a maximum-capacity forest on the
actual row and column vertices. -/
theorem computed_spec (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (hW : 1≤W) :
    computed r c b W≤cellGraph (small b W) ∧ (computed r c b W).IsAcyclic ∧
    ∀ F : SimpleGraph (Fin m⊕Fin n),F≤cellGraph (small b W) → F.IsAcyclic →
      weight F (capacity b)≤weight (computed r c b W) (capacity b) := by
  have ht := execute_optimal (graph b W) ⊥ (capacities b)
    (catalog (NetworkVertexCode.data r c b,W)) (catalog_correct r c b W)
    (capacity_positive b W hW) (MaximumForestExchange.bottom_extendible _ _)
  have hzero (d : DecidableRel (⊥ : SimpleGraph (Fin (m+n))).Adj) :
      @graphCode (m+n) ⊥ d=ForestGreedyProgram.emptyGraph (NetworkVertexCode.data r c b,W) := by
    symm
    simp only [ForestGreedyProgram.emptyGraph,vertexCount_code,DirectedBFSCode.range_eq_map,
      ←List.ofFn_eq_map,List.map_ofFn,graphCode]
    apply congrArg List.ofFn
    funext v
    simp [adjacencyRow]
  dsimp only at ht
  rw [hzero] at ht
  change let T:=decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W));
    T≤graph b W ∧ T.IsAcyclic ∧
      ∀ H,H≤graph b W → H.IsAcyclic → weight H (capacities b)≤weight T (capacities b) at ht
  dsimp only at ht
  let T : SimpleGraph (Fin (m+n)) :=
    decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W))
  have hback : (T.comap vertexEquiv).map vertexEquiv.toEmbedding=T := by
    rw [←SimpleGraph.comap_symm]
    ext u v
    change T.Adj (vertexEquiv (vertexEquiv.symm u))
      (vertexEquiv (vertexEquiv.symm v)) ↔ T.Adj u v
    simp only [Equiv.apply_symm_apply]
  have hT : T.comap vertexEquiv≤cellGraph (small b W) := by
    intro u v huv
    exact (SimpleGraph.map_adj_apply (G:=cellGraph (small b W))
      (f:=vertexEquiv.toEmbedding) (a:=u) (b:=v)).mp (ht.1 huv)
  refine ⟨hT,ht.2.1.of_comap vertexEquiv.toEmbedding,?_⟩
  intro F hF hac
  have hle : F.map vertexEquiv.toEmbedding≤graph b W := map_monotone _ hF
  have ha : (F.map vertexEquiv.toEmbedding).IsAcyclic :=
    (SimpleGraph.Iso.map vertexEquiv F).isAcyclic_iff.mp hac
  have hw := ht.2.2 (F.map vertexEquiv.toEmbedding) hle ha
  have h1 := weight_transport vertexEquiv F (capacity b)
  have h2 := weight_transport vertexEquiv (T.comap vertexEquiv) (capacity b)
  rw [hback] at h2
  exact h1.symm.trans_le (hw.trans_eq h2)

end ContingencyTables.ComputedLargeForest

end OAI
