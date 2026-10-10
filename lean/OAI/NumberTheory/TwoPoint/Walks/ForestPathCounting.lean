import OAI.NumberTheory.TwoPoint.Walks.ForestPathCode
import OAI.NumberTheory.TwoPoint.Walks.ColumnCode

namespace OAI

/-!
# Counting all realizable numbered path families

The union is over every finite acyclic graph, not a single graph with fixed
numerical coefficients. A typed forest shape and two endpoints per segment
determine the entire family of numbered paths.
-/

namespace TwoPointCorrelations

open SimpleGraph

/-- A finite realization of the regular segments in one column. -/
structure ForestPathData (N segments : ℕ) where
  vertices : ℕ
  vertex_bound : vertices ≤ N
  graph : SimpleGraph (Fin vertices)
  acyclic : graph.IsAcyclic
  tree : BinaryTree (Fin vertices)
  nodup : (forestNodes tree).Nodup
  cover : ∀ v, v ∈ forestNodes tree
  adjacent : ∀ a b, forestAdjacent tree a b ↔ graph.Adj a b
  color : Fin vertices → Bool
  start : Fin segments → Fin vertices
  finish : Fin segments → Fin vertices
  walk : ∀ i, graph.Walk (start i) (finish i)
  reduced : ∀ i, List.IsChain (· ≠ ·) (walk i).edges

namespace ForestPathData

variable {N segments : ℕ}

def pattern (d : ForestPathData N segments) : Fin segments → List ℕ :=
  fun i => (d.walk i).support.map (fun v => (forestNodes d.tree).idxOf v)

def shape (d : ForestPathData N segments) : {t : BinaryTree Bool // t.numNodes ≤ N} :=
  ⟨d.tree.map d.color, by
    rw [forest_numNodes_map, forest_representation_numNodes d.tree d.nodup d.cover]
    simpa only [Fintype.card_fin] using d.vertex_bound⟩

def index (d : ForestPathData N segments) (v : Fin d.vertices) : Fin N :=
  ⟨(forestNodes d.tree).idxOf v, by
    have hlt := List.idxOf_lt_length_iff.mpr (d.cover v)
    rw [forestNodes_length, forest_representation_numNodes d.tree d.nodup d.cover,
      Fintype.card_fin] at hlt
    exact hlt.trans_le d.vertex_bound⟩

abbrev Code (N segments : ℕ) :=
  {t : BinaryTree Bool // t.numNodes ≤ N} × (Fin segments → Fin N × Fin N)

def code (d : ForestPathData N segments) : Code N segments :=
  (d.shape, fun i => (d.index (d.start i), d.index (d.finish i)))

/-- No numerical vertex label survives in the code. -/
theorem pattern_eq_of_code_eq (d e : ForestPathData N segments) (h : d.code = e.code) :
    d.pattern = e.pattern := by
  have hshape : d.tree.map (fun _ => ()) = e.tree.map (fun _ => ()) := by
    have ht : d.tree.map d.color = e.tree.map e.color :=
      congrArg Subtype.val (congrArg Prod.fst h)
    have hu := congrArg (fun t => t.map (fun _ => ())) ht
    simpa only [← BinaryTree.comp_map, Function.comp_def] using hu
  have hend := congrArg Prod.snd h
  funext i
  apply represented_walk_same_endpoints d.tree e.tree d.nodup d.cover e.nodup e.cover
    d.adjacent e.adjacent hshape d.acyclic e.acyclic (d.walk i) (e.walk i)
    (d.reduced i) (e.reduced i)
  · exact congrArg Fin.val (congrArg Prod.fst (congrFun hend i))
  · exact congrArg Fin.val (congrArg Prod.snd (congrFun hend i))

theorem card_code_le (N segments : ℕ) :
    Fintype.card (Code N segments) ≤ 2 ^ (3 * N + 1) * N ^ (2 * segments) := by
  have ht : Fintype.card {t : BinaryTree Bool // t.numNodes ≤ N} ≤ 2 ^ (3 * N + 1) := by
    simpa only [Nat.card_eq_fintype_card] using card_bounded_forests N
  simp only [Code, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  calc
    _ ≤ 2 ^ (3 * N + 1) * (N * N) ^ segments := Nat.mul_le_mul_right _ ht
    _ = _ := by rw [← pow_two, ← pow_mul]

end ForestPathData

/-- This range includes the union over all finite graph realizations. -/
def RealizableForestPaths (N segments : ℕ) :=
  {p : Fin segments → List ℕ // ∃ d : ForestPathData N segments, d.pattern = p}

noncomputable def realizableForestPathCode {N segments : ℕ}
    (p : RealizableForestPaths N segments) : ForestPathData.Code N segments :=
  p.property.choose.code

theorem realizableForestPathCode_injective (N segments : ℕ) :
    Function.Injective (@realizableForestPathCode N segments) := by
  intro p q h
  apply Subtype.ext
  have hp := p.property.choose_spec
  have hq := q.property.choose_spec
  exact hp.symm.trans ((ForestPathData.pattern_eq_of_code_eq _ _ h).trans hq)

/-- A coefficient-independent bound for all reduced regular path families. -/
theorem card_realizable_forest_paths (N segments : ℕ) :
    Nat.card (RealizableForestPaths N segments) ≤
      2 ^ (3 * N + 1) * N ^ (2 * segments) := by
  have h := Nat.card_le_card_of_injective (@realizableForestPathCode N segments)
    (realizableForestPathCode_injective N segments)
  exact h.trans (by
    simpa only [Nat.card_eq_fintype_card] using ForestPathData.card_code_le N segments)

end TwoPointCorrelations

end OAI
