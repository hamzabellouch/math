import OAI.Combinatorics.Ramsey.CycleClique.Construction.LayoutCertificate
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateMatrixChunks
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FastCertificateMatrix
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FastLayoutGraph

namespace OAI

namespace CycleClique.Construction.Certificates

def k11t7p22 : LayoutCertificate 11 where
  chains := [[0], [1, 2, 3], [4, 5, 6, 7, 8, 9, 10]]
  clique := {0, 1, 3, 4, 6, 8, 10}
  templates := [⟨0, 2, [[4, 5, 6, 7, 8]], [], [1], 1, 4⟩,
    ⟨0, 5, [[1, 2, 3], [6, 7, 8]], [], [4], 1, 3⟩,
    ⟨0, 7, [[1, 2, 3]], [], [6, 5, 4], 1, 4⟩,
    ⟨0, 9, [[1, 2, 3], [4, 5, 6]], [], [8], 1, 3⟩,
    ⟨1, 2, [[4, 5, 6, 7, 8]], [], [3], 1, 4⟩,
    ⟨1, 5, [[6, 7, 8]], [3, 2], [4], 1, 4⟩,
    ⟨1, 7, [], [3, 2], [6, 5, 4], 1, 5⟩,
    ⟨1, 9, [[4, 5, 6]], [3, 2], [8], 1, 4⟩,
    ⟨2, 3, [[4, 5, 6, 7, 8]], [1], [], 1, 4⟩,
    ⟨2, 4, [], [1], [5, 6, 7, 8], 1, 5⟩,
    ⟨2, 5, [[6, 7, 8]], [1], [4], 1, 5⟩,
    ⟨2, 7, [], [1], [6, 5, 4], 1, 6⟩,
    ⟨2, 9, [[4, 5, 6]], [1], [8], 1, 5⟩,
    ⟨3, 5, [[6, 7, 8]], [1, 2], [4], 1, 4⟩,
    ⟨3, 7, [], [1, 2], [6, 5, 4], 1, 5⟩,
    ⟨3, 9, [[4, 5, 6]], [1, 2], [8], 1, 4⟩,
    ⟨4, 5, [[1, 2, 3]], [], [6, 7, 8], 1, 4⟩,
    ⟨4, 7, [[1, 2, 3]], [6, 5], [8], 1, 4⟩,
    ⟨4, 9, [[1, 2, 3]], [6, 5], [8], 1, 4⟩,
    ⟨5, 7, [], [4], [6], 2, 8⟩,
    ⟨5, 7, [[1, 2, 3]], [4], [6], 1, 5⟩,
    ⟨5, 9, [], [4], [8], 2, 8⟩,
    ⟨5, 9, [[1, 2, 3]], [4], [8], 1, 5⟩,
    ⟨7, 9, [], [6], [8], 2, 8⟩,
    ⟨7, 9, [[1, 2, 3]], [6], [8], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 0), (2, 2), (5, 3), (7, 3), (9, 3)}⟩


private def k11t7p22_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, false, true, true, false, true, false, true, false, true],
    #[true, false, true, true, true, false, true, false, true, false, true],
    #[false, true, false, true, false, false, false, false, false, false, false],
    #[true, true, true, false, true, false, true, false, true, false, true],
    #[true, true, false, true, false, true, true, false, true, false, true],
    #[false, false, false, false, true, false, true, false, false, false, false],
    #[true, true, false, true, true, true, false, true, true, false, true],
    #[false, false, false, false, false, false, true, false, true, false, false],
    #[true, true, false, true, true, false, true, true, false, true, true],
    #[false, false, false, false, false, false, false, false, true, false, true],
    #[true, true, false, true, true, false, true, false, true, true, false]]

private theorem k11t7p22_adjacency_row_0 : ∀ j : Fin 11,
    k11t7p22.graph.Adj 0 j ↔ adjacencyTableLookup k11t7p22_adjacencyTable 0 j.val = true := by decide

private theorem k11t7p22_adjacency_row_1 : ∀ j : Fin 11,
    k11t7p22.graph.Adj 1 j ↔ adjacencyTableLookup k11t7p22_adjacencyTable 1 j.val = true := by decide

private theorem k11t7p22_adjacency_row_2 : ∀ j : Fin 11,
    k11t7p22.graph.Adj 2 j ↔ adjacencyTableLookup k11t7p22_adjacencyTable 2 j.val = true := by decide

private theorem k11t7p22_adjacency_row_3 : ∀ j : Fin 11,
    k11t7p22.graph.Adj 3 j ↔ adjacencyTableLookup k11t7p22_adjacencyTable 3 j.val = true := by decide

private theorem k11t7p22_adjacency_row_4 : ∀ j : Fin 11,
    k11t7p22.graph.Adj 4 j ↔ adjacencyTableLookup k11t7p22_adjacencyTable 4 j.val = true := by decide

private theorem k11t7p22_adjacency_row_5 : ∀ j : Fin 11,
    k11t7p22.graph.Adj 5 j ↔ adjacencyTableLookup k11t7p22_adjacencyTable 5 j.val = true := by decide

private theorem k11t7p22_adjacency_row_6 : ∀ j : Fin 11,
    k11t7p22.graph.Adj 6 j ↔ adjacencyTableLookup k11t7p22_adjacencyTable 6 j.val = true := by decide

private theorem k11t7p22_adjacency_row_7 : ∀ j : Fin 11,
    k11t7p22.graph.Adj 7 j ↔ adjacencyTableLookup k11t7p22_adjacencyTable 7 j.val = true := by decide

private theorem k11t7p22_adjacency_row_8 : ∀ j : Fin 11,
    k11t7p22.graph.Adj 8 j ↔ adjacencyTableLookup k11t7p22_adjacencyTable 8 j.val = true := by decide

private theorem k11t7p22_adjacency_row_9 : ∀ j : Fin 11,
    k11t7p22.graph.Adj 9 j ↔ adjacencyTableLookup k11t7p22_adjacencyTable 9 j.val = true := by decide

private theorem k11t7p22_adjacency_row_10 : ∀ j : Fin 11,
    k11t7p22.graph.Adj 10 j ↔ adjacencyTableLookup k11t7p22_adjacencyTable 10 j.val = true := by decide

private theorem k11t7p22_adjacency_eq : ∀ i j : Fin 11,
    k11t7p22.graph.Adj i j ↔ adjacencyTableLookup k11t7p22_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t7p22_adjacency_row_0 j

  · exact k11t7p22_adjacency_row_1 j

  · exact k11t7p22_adjacency_row_2 j

  · exact k11t7p22_adjacency_row_3 j

  · exact k11t7p22_adjacency_row_4 j

  · exact k11t7p22_adjacency_row_5 j

  · exact k11t7p22_adjacency_row_6 j

  · exact k11t7p22_adjacency_row_7 j

  · exact k11t7p22_adjacency_row_8 j

  · exact k11t7p22_adjacency_row_9 j

  · exact k11t7p22_adjacency_row_10 j

private def k11t7p22_tableGraph : SimpleGraph (Fin 11) :=
  adjacencyTableGraph k11t7p22.graph k11t7p22_adjacencyTable k11t7p22_adjacency_eq

private instance k11t7p22_tableGraph_decidableAdj :
    DecidableRel k11t7p22_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t7p22_adjacencyTable i.val j.val = true))

private theorem k11t7p22_tableGraph_eq : k11t7p22_tableGraph = k11t7p22.graph :=
  adjacencyTableGraph_eq k11t7p22.graph k11t7p22_adjacencyTable k11t7p22_adjacency_eq

private def k11t7p22_state_0 : ForbiddenMatrix 11 :=
  fun i j => ((#[#[∅, ∅, Finset.Icc 1 4, ∅, ∅, {1, 2, 3}, ∅, Finset.Icc 1 4, ∅, {1, 2, 3}, ∅],
    #[∅, ∅, Finset.Icc 1 4, ∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅],
    #[∅, ∅, Finset.Icc 1 4, ∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 4, ∅],
    #[∅, ∅, Finset.Icc 1 5, ∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, ∅, ∅, Finset.Icc 1 8, ∅, Finset.Icc 1 8, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 8, ∅, ∅, ∅, Finset.Icc 1 8, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 8, ∅, Finset.Icc 1 8, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t7p22_decode_entry_0 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p22_decode_entry_1 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t7p22_decode_entry_2 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p22_decode_entry_3 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t7p22_decode_entry_4 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p22_decode_entry_5 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p22_decode_entry_6 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p22_decode_entry_7 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p22_decode_entry_8 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p22_decode_entry_9 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p22_decode_entry_10 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p22_decode_entry_11 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t7p22_decode_entry_12 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p22_decode_entry_13 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p22_decode_entry_14 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p22_decode_entry_15 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p22_decode_entry_16 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p22_decode_entry_17 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p22_decode_entry_18 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p22_decode_entry_19 : decode 12 508 = Finset.Icc 2 8 := by decide

private theorem k11t7p22_decode_entry_20 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p22_decode_entry_21 : decode 12 508 = Finset.Icc 2 8 := by decide

private theorem k11t7p22_decode_entry_22 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p22_decode_entry_23 : decode 12 508 = Finset.Icc 2 8 := by decide

private theorem k11t7p22_decode_entry_24 : decode 12 62 = Finset.Icc 1 5 := by decide

private def k11t7p22_mask_entries_0 : List (TemplateData (Fin 11) × ℕ) := [(⟨0, 2, [[4, 5, 6, 7, 8]], [], [1], 1, 4⟩, 30), (⟨0, 5, [[1, 2, 3], [6, 7, 8]], [], [4], 1, 3⟩, 14), (⟨0, 7, [[1, 2, 3]], [], [6, 5, 4], 1, 4⟩, 30), (⟨0, 9, [[1, 2, 3], [4, 5, 6]], [], [8], 1, 3⟩, 14), (⟨1, 2, [[4, 5, 6, 7, 8]], [], [3], 1, 4⟩, 30), (⟨1, 5, [[6, 7, 8]], [3, 2], [4], 1, 4⟩, 30), (⟨1, 7, [], [3, 2], [6, 5, 4], 1, 5⟩, 62), (⟨1, 9, [[4, 5, 6]], [3, 2], [8], 1, 4⟩, 30), (⟨2, 3, [[4, 5, 6, 7, 8]], [1], [], 1, 4⟩, 30), (⟨2, 4, [], [1], [5, 6, 7, 8], 1, 5⟩, 62), (⟨2, 5, [[6, 7, 8]], [1], [4], 1, 5⟩, 62), (⟨2, 7, [], [1], [6, 5, 4], 1, 6⟩, 126), (⟨2, 9, [[4, 5, 6]], [1], [8], 1, 5⟩, 62), (⟨3, 5, [[6, 7, 8]], [1, 2], [4], 1, 4⟩, 30), (⟨3, 7, [], [1, 2], [6, 5, 4], 1, 5⟩, 62), (⟨3, 9, [[4, 5, 6]], [1, 2], [8], 1, 4⟩, 30), (⟨4, 5, [[1, 2, 3]], [], [6, 7, 8], 1, 4⟩, 30), (⟨4, 7, [[1, 2, 3]], [6, 5], [8], 1, 4⟩, 30), (⟨4, 9, [[1, 2, 3]], [6, 5], [8], 1, 4⟩, 30), (⟨5, 7, [], [4], [6], 2, 8⟩, 508), (⟨5, 7, [[1, 2, 3]], [4], [6], 1, 5⟩, 62), (⟨5, 9, [], [4], [8], 2, 8⟩, 508), (⟨5, 9, [[1, 2, 3]], [4], [8], 1, 5⟩, 62), (⟨7, 9, [], [6], [8], 2, 8⟩, 508), (⟨7, 9, [[1, 2, 3]], [6], [8], 1, 5⟩, 62)]

private theorem k11t7p22_decode_entries_0 : ∀ Tb ∈ k11t7p22_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t7p22_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t7p22_decode_entry_0, k11t7p22_decode_entry_1, k11t7p22_decode_entry_2, k11t7p22_decode_entry_3, k11t7p22_decode_entry_4, k11t7p22_decode_entry_5, k11t7p22_decode_entry_6, k11t7p22_decode_entry_7, k11t7p22_decode_entry_8, k11t7p22_decode_entry_9, k11t7p22_decode_entry_10, k11t7p22_decode_entry_11, k11t7p22_decode_entry_12, k11t7p22_decode_entry_13, k11t7p22_decode_entry_14, k11t7p22_decode_entry_15, k11t7p22_decode_entry_16, k11t7p22_decode_entry_17, k11t7p22_decode_entry_18, k11t7p22_decode_entry_19, k11t7p22_decode_entry_20, k11t7p22_decode_entry_21, k11t7p22_decode_entry_22, k11t7p22_decode_entry_23, k11t7p22_decode_entry_24⟩

private def k11t7p22_mask_block_0 : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 0, 30, 0, 0, 14, 0, 30, 0, 14, 0],
    #[0, 0, 30, 0, 0, 30, 0, 62, 0, 30, 0],
    #[30, 30, 0, 30, 62, 62, 0, 126, 0, 62, 0],
    #[0, 0, 30, 0, 0, 30, 0, 62, 0, 30, 0],
    #[0, 0, 62, 0, 0, 30, 0, 30, 0, 30, 0],
    #[14, 30, 62, 30, 30, 0, 0, 510, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[30, 62, 126, 62, 30, 510, 0, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[14, 30, 62, 30, 30, 510, 0, 510, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t7p22_mask_block_0_eq_row_0 : ∀ j : Fin 11, (templateMaskMatrix k11t7p22_mask_entries_0) 0 j = k11t7p22_mask_block_0 0 j := by decide

private theorem k11t7p22_mask_block_0_eq_row_1 : ∀ j : Fin 11, (templateMaskMatrix k11t7p22_mask_entries_0) 1 j = k11t7p22_mask_block_0 1 j := by decide

private theorem k11t7p22_mask_block_0_eq_row_2 : ∀ j : Fin 11, (templateMaskMatrix k11t7p22_mask_entries_0) 2 j = k11t7p22_mask_block_0 2 j := by decide

private theorem k11t7p22_mask_block_0_eq_row_3 : ∀ j : Fin 11, (templateMaskMatrix k11t7p22_mask_entries_0) 3 j = k11t7p22_mask_block_0 3 j := by decide

private theorem k11t7p22_mask_block_0_eq_row_4 : ∀ j : Fin 11, (templateMaskMatrix k11t7p22_mask_entries_0) 4 j = k11t7p22_mask_block_0 4 j := by decide

private theorem k11t7p22_mask_block_0_eq_row_5 : ∀ j : Fin 11, (templateMaskMatrix k11t7p22_mask_entries_0) 5 j = k11t7p22_mask_block_0 5 j := by decide

private theorem k11t7p22_mask_block_0_eq_row_6 : ∀ j : Fin 11, (templateMaskMatrix k11t7p22_mask_entries_0) 6 j = k11t7p22_mask_block_0 6 j := by decide

private theorem k11t7p22_mask_block_0_eq_row_7 : ∀ j : Fin 11, (templateMaskMatrix k11t7p22_mask_entries_0) 7 j = k11t7p22_mask_block_0 7 j := by decide

private theorem k11t7p22_mask_block_0_eq_row_8 : ∀ j : Fin 11, (templateMaskMatrix k11t7p22_mask_entries_0) 8 j = k11t7p22_mask_block_0 8 j := by decide

private theorem k11t7p22_mask_block_0_eq_row_9 : ∀ j : Fin 11, (templateMaskMatrix k11t7p22_mask_entries_0) 9 j = k11t7p22_mask_block_0 9 j := by decide

private theorem k11t7p22_mask_block_0_eq_row_10 : ∀ j : Fin 11, (templateMaskMatrix k11t7p22_mask_entries_0) 10 j = k11t7p22_mask_block_0 10 j := by decide

private theorem k11t7p22_mask_block_0_eq : (templateMaskMatrix k11t7p22_mask_entries_0) = k11t7p22_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t7p22_mask_block_0_eq_row_0 j

  · exact k11t7p22_mask_block_0_eq_row_1 j

  · exact k11t7p22_mask_block_0_eq_row_2 j

  · exact k11t7p22_mask_block_0_eq_row_3 j

  · exact k11t7p22_mask_block_0_eq_row_4 j

  · exact k11t7p22_mask_block_0_eq_row_5 j

  · exact k11t7p22_mask_block_0_eq_row_6 j

  · exact k11t7p22_mask_block_0_eq_row_7 j

  · exact k11t7p22_mask_block_0_eq_row_8 j

  · exact k11t7p22_mask_block_0_eq_row_9 j

  · exact k11t7p22_mask_block_0_eq_row_10 j

private def k11t7p22_mask_entries : List (TemplateData (Fin 11) × ℕ) := k11t7p22_mask_entries_0

private theorem k11t7p22_decode_entries : ∀ Tb ∈ k11t7p22_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t7p22_decode_entries_0

private theorem k11t7p22_mask_entries_map : k11t7p22_mask_entries.map Prod.fst = k11t7p22.templates := by rfl

private def k11t7p22_template_mask : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 0, 30, 0, 0, 14, 0, 30, 0, 14, 0],
    #[0, 0, 30, 0, 0, 30, 0, 62, 0, 30, 0],
    #[30, 30, 0, 30, 62, 62, 0, 126, 0, 62, 0],
    #[0, 0, 30, 0, 0, 30, 0, 62, 0, 30, 0],
    #[0, 0, 62, 0, 0, 30, 0, 30, 0, 30, 0],
    #[14, 30, 62, 30, 30, 0, 0, 510, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[30, 62, 126, 62, 30, 510, 0, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[14, 30, 62, 30, 30, 510, 0, 510, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t7p22_mask_merged_eq_row_0 : ∀ j : Fin 11, (fun i j => k11t7p22_mask_block_0 i j) 0 j = k11t7p22_template_mask 0 j := by decide

private theorem k11t7p22_mask_merged_eq_row_1 : ∀ j : Fin 11, (fun i j => k11t7p22_mask_block_0 i j) 1 j = k11t7p22_template_mask 1 j := by decide

private theorem k11t7p22_mask_merged_eq_row_2 : ∀ j : Fin 11, (fun i j => k11t7p22_mask_block_0 i j) 2 j = k11t7p22_template_mask 2 j := by decide

private theorem k11t7p22_mask_merged_eq_row_3 : ∀ j : Fin 11, (fun i j => k11t7p22_mask_block_0 i j) 3 j = k11t7p22_template_mask 3 j := by decide

private theorem k11t7p22_mask_merged_eq_row_4 : ∀ j : Fin 11, (fun i j => k11t7p22_mask_block_0 i j) 4 j = k11t7p22_template_mask 4 j := by decide

private theorem k11t7p22_mask_merged_eq_row_5 : ∀ j : Fin 11, (fun i j => k11t7p22_mask_block_0 i j) 5 j = k11t7p22_template_mask 5 j := by decide

private theorem k11t7p22_mask_merged_eq_row_6 : ∀ j : Fin 11, (fun i j => k11t7p22_mask_block_0 i j) 6 j = k11t7p22_template_mask 6 j := by decide

private theorem k11t7p22_mask_merged_eq_row_7 : ∀ j : Fin 11, (fun i j => k11t7p22_mask_block_0 i j) 7 j = k11t7p22_template_mask 7 j := by decide

private theorem k11t7p22_mask_merged_eq_row_8 : ∀ j : Fin 11, (fun i j => k11t7p22_mask_block_0 i j) 8 j = k11t7p22_template_mask 8 j := by decide

private theorem k11t7p22_mask_merged_eq_row_9 : ∀ j : Fin 11, (fun i j => k11t7p22_mask_block_0 i j) 9 j = k11t7p22_template_mask 9 j := by decide

private theorem k11t7p22_mask_merged_eq_row_10 : ∀ j : Fin 11, (fun i j => k11t7p22_mask_block_0 i j) 10 j = k11t7p22_template_mask 10 j := by decide

private theorem k11t7p22_mask_merged_eq : (fun i j => k11t7p22_mask_block_0 i j) = k11t7p22_template_mask := by
  funext i j
  fin_cases i

  · exact k11t7p22_mask_merged_eq_row_0 j

  · exact k11t7p22_mask_merged_eq_row_1 j

  · exact k11t7p22_mask_merged_eq_row_2 j

  · exact k11t7p22_mask_merged_eq_row_3 j

  · exact k11t7p22_mask_merged_eq_row_4 j

  · exact k11t7p22_mask_merged_eq_row_5 j

  · exact k11t7p22_mask_merged_eq_row_6 j

  · exact k11t7p22_mask_merged_eq_row_7 j

  · exact k11t7p22_mask_merged_eq_row_8 j

  · exact k11t7p22_mask_merged_eq_row_9 j

  · exact k11t7p22_mask_merged_eq_row_10 j

private theorem k11t7p22_template_mask_eq : templateMaskMatrix k11t7p22_mask_entries = k11t7p22_template_mask := by
  funext i j
  change templateMaskMatrix (k11t7p22_mask_entries_0) i j = _
  simp only [k11t7p22_mask_block_0_eq]
  exact congrFun (congrFun k11t7p22_mask_merged_eq i) j

private theorem k11t7p22_initial_decoded_eq_row_0 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) 0 j = k11t7p22_state_0 0 j := by decide

private theorem k11t7p22_initial_decoded_eq_row_1 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) 1 j = k11t7p22_state_0 1 j := by decide

private theorem k11t7p22_initial_decoded_eq_row_2 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) 2 j = k11t7p22_state_0 2 j := by decide

private theorem k11t7p22_initial_decoded_eq_row_3 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) 3 j = k11t7p22_state_0 3 j := by decide

private theorem k11t7p22_initial_decoded_eq_row_4 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) 4 j = k11t7p22_state_0 4 j := by decide

private theorem k11t7p22_initial_decoded_eq_row_5 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) 5 j = k11t7p22_state_0 5 j := by decide

private theorem k11t7p22_initial_decoded_eq_row_6 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) 6 j = k11t7p22_state_0 6 j := by decide

private theorem k11t7p22_initial_decoded_eq_row_7 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) 7 j = k11t7p22_state_0 7 j := by decide

private theorem k11t7p22_initial_decoded_eq_row_8 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) 8 j = k11t7p22_state_0 8 j := by decide

private theorem k11t7p22_initial_decoded_eq_row_9 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) 9 j = k11t7p22_state_0 9 j := by decide

private theorem k11t7p22_initial_decoded_eq_row_10 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) 10 j = k11t7p22_state_0 10 j := by decide

private theorem k11t7p22_initial_decoded_eq : (fun i j => decode 12 (k11t7p22_template_mask i j) ∪ requiredMatrix 11 k11t7p22.required i j) = k11t7p22_state_0 := by
  funext i j
  fin_cases i

  · exact k11t7p22_initial_decoded_eq_row_0 j

  · exact k11t7p22_initial_decoded_eq_row_1 j

  · exact k11t7p22_initial_decoded_eq_row_2 j

  · exact k11t7p22_initial_decoded_eq_row_3 j

  · exact k11t7p22_initial_decoded_eq_row_4 j

  · exact k11t7p22_initial_decoded_eq_row_5 j

  · exact k11t7p22_initial_decoded_eq_row_6 j

  · exact k11t7p22_initial_decoded_eq_row_7 j

  · exact k11t7p22_initial_decoded_eq_row_8 j

  · exact k11t7p22_initial_decoded_eq_row_9 j

  · exact k11t7p22_initial_decoded_eq_row_10 j

private theorem k11t7p22_initial_eq : k11t7p22.initialMatrix 11 = k11t7p22_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t7p22_mask_entries k11t7p22_decode_entries
  rw [k11t7p22_mask_entries_map, k11t7p22_template_mask_eq] at h
  funext i j
  change templateMatrix k11t7p22.templates i j ∪ requiredMatrix 11 k11t7p22.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t7p22_initial_decoded_eq i) j

private theorem k11t7p22_closure_0 : ClosureCheck k11t7p22.graph k11t7p22_state_0 11 7 [] := by trivial

private theorem k11t7p22_matrix_eq : k11t7p22.matrix 11 = k11t7p22_state_0 := by
  change closureMatrix (k11t7p22.initialMatrix 11) _ = _
  rw [k11t7p22_initial_eq]
  change closureMatrix k11t7p22_state_0 [] = _
  rfl

private theorem k11t7p22_part_0 : k11t7p22.chains.flatten = List.finRange _ := by decide

private theorem k11t7p22_part_1 : k11t7p22.chains.map List.length = ([[], [1], [1, 1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t7p22_part_2 : k11t7p22.chains.map (fun l => l.map (fun i => decide (i ∈ k11t7p22.clique))) = ([[], [1], [1, 1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k11t7p22_templates_item_0 : (⟨0, 2, [[4, 5, 6, 7, 8]], [], [1], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_1 : (⟨0, 5, [[1, 2, 3], [6, 7, 8]], [], [4], 1, 3⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_2 : (⟨0, 7, [[1, 2, 3]], [], [6, 5, 4], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_3 : (⟨0, 9, [[1, 2, 3], [4, 5, 6]], [], [8], 1, 3⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_4 : (⟨1, 2, [[4, 5, 6, 7, 8]], [], [3], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_5 : (⟨1, 5, [[6, 7, 8]], [3, 2], [4], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_6 : (⟨1, 7, [], [3, 2], [6, 5, 4], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_7 : (⟨1, 9, [[4, 5, 6]], [3, 2], [8], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_8 : (⟨2, 3, [[4, 5, 6, 7, 8]], [1], [], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_9 : (⟨2, 4, [], [1], [5, 6, 7, 8], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_10 : (⟨2, 5, [[6, 7, 8]], [1], [4], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_11 : (⟨2, 7, [], [1], [6, 5, 4], 1, 6⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_12 : (⟨2, 9, [[4, 5, 6]], [1], [8], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_13 : (⟨3, 5, [[6, 7, 8]], [1, 2], [4], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_14 : (⟨3, 7, [], [1, 2], [6, 5, 4], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_15 : (⟨3, 9, [[4, 5, 6]], [1, 2], [8], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_16 : (⟨4, 5, [[1, 2, 3]], [], [6, 7, 8], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_17 : (⟨4, 7, [[1, 2, 3]], [6, 5], [8], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_18 : (⟨4, 9, [[1, 2, 3]], [6, 5], [8], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_19 : (⟨5, 7, [], [4], [6], 2, 8⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_20 : (⟨5, 7, [[1, 2, 3]], [4], [6], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_21 : (⟨5, 9, [], [4], [8], 2, 8⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_22 : (⟨5, 9, [[1, 2, 3]], [4], [8], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_23 : (⟨7, 9, [], [6], [8], 2, 8⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_item_24 : (⟨7, 9, [[1, 2, 3]], [6], [8], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p22_tableGraph_eq]
  decide

private theorem k11t7p22_templates_fast_block_0_check : ∀ T ∈ k11t7p22_mask_entries_0.map Prod.fst, T.Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t7p22_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t7p22_templates_item_0, k11t7p22_templates_item_1, k11t7p22_templates_item_2, k11t7p22_templates_item_3, k11t7p22_templates_item_4, k11t7p22_templates_item_5, k11t7p22_templates_item_6, k11t7p22_templates_item_7, k11t7p22_templates_item_8, k11t7p22_templates_item_9, k11t7p22_templates_item_10, k11t7p22_templates_item_11, k11t7p22_templates_item_12, k11t7p22_templates_item_13, k11t7p22_templates_item_14, k11t7p22_templates_item_15, k11t7p22_templates_item_16, k11t7p22_templates_item_17, k11t7p22_templates_item_18, k11t7p22_templates_item_19, k11t7p22_templates_item_20, k11t7p22_templates_item_21, k11t7p22_templates_item_22, k11t7p22_templates_item_23, k11t7p22_templates_item_24⟩

private theorem k11t7p22_part_3 : ∀ T ∈ k11t7p22.templates, T.Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t7p22_mask_entries_0.map Prod.fst), T.Check k11t7p22.graph k11t7p22.clique 11 (patternAmount ([[], [1], [1, 1, 1]] : List (List ℕ))) (([[], [1], [1, 1, 1]] : List (List ℕ)).map List.length).sum
  exact k11t7p22_templates_fast_block_0_check

private theorem k11t7p22_part_4 : ∀ p ∈ k11t7p22.required, p.Check k11t7p22.graph 11 := by decide

private theorem k11t7p22_part_5 : ClosureCheck k11t7p22.graph (k11t7p22.initialMatrix 11) 11 7 k11t7p22.closure := by
  rw [k11t7p22_initial_eq]
  exact k11t7p22_closure_0

private theorem k11t7p22_part_6 : k11t7p22.bad.Check k11t7p22.graph (k11t7p22.matrix 11) 11 7 := by
  rw [k11t7p22_matrix_eq]
  decide

theorem k11t7p22_check : k11t7p22.Check 11 7 [[], [1], [1, 1, 1]] :=
  ⟨k11t7p22_part_0, k11t7p22_part_1, k11t7p22_part_2, k11t7p22_part_3, k11t7p22_part_4, k11t7p22_part_5, k11t7p22_part_6⟩
def k11t7p23 : LayoutCertificate 11 where
  chains := [[0], [1, 2, 3, 4, 5], [6, 7, 8, 9, 10]]
  clique := {0, 1, 3, 5, 6, 8, 10}
  templates := [⟨0, 2, [[3, 4, 5], [6, 7, 8]], [], [1], 1, 3⟩,
    ⟨0, 4, [[6, 7, 8]], [], [3, 2, 1], 1, 4⟩,
    ⟨0, 7, [[1, 2, 3, 4, 5]], [], [6], 1, 4⟩,
    ⟨0, 9, [[1, 2, 3, 4, 5]], [], [8], 1, 4⟩,
    ⟨1, 2, [[6, 7, 8]], [], [3, 4, 5], 1, 4⟩,
    ⟨1, 4, [[6, 7, 8]], [3, 2], [5], 1, 4⟩,
    ⟨1, 7, [], [5, 4, 3, 2], [6], 1, 5⟩,
    ⟨1, 9, [], [5, 4, 3, 2], [8], 1, 5⟩,
    ⟨2, 3, [[6, 7, 8]], [1], [4, 5], 1, 4⟩,
    ⟨2, 4, [[6, 7, 8]], [1], [3], 1, 5⟩,
    ⟨2, 5, [[6, 7, 8]], [1], [4, 3], 1, 4⟩,
    ⟨2, 7, [[3, 4, 5]], [1], [6], 1, 5⟩,
    ⟨2, 9, [[3, 4, 5]], [1], [8], 1, 5⟩,
    ⟨3, 4, [[6, 7, 8]], [1, 2], [5], 1, 4⟩,
    ⟨3, 7, [[8, 9, 10]], [1, 2], [6], 1, 4⟩,
    ⟨3, 9, [], [1, 2], [8, 7, 6], 1, 5⟩,
    ⟨4, 5, [[6, 7, 8]], [1, 2, 3], [], 1, 4⟩,
    ⟨4, 7, [], [1, 2, 3], [6], 1, 6⟩,
    ⟨4, 9, [], [1, 2, 3], [8], 1, 6⟩,
    ⟨5, 7, [], [1, 2, 3, 4], [6], 1, 5⟩,
    ⟨5, 9, [], [1, 2, 3, 4], [8], 1, 5⟩,
    ⟨7, 9, [], [6], [8], 2, 8⟩,
    ⟨7, 9, [[1, 2, 3]], [6], [8], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 0), (2, 2), (4, 3), (7, 3), (9, 3)}⟩


private def k11t7p23_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, false, true, false, true, true, false, true, false, true],
    #[true, false, true, true, false, true, true, false, true, false, true],
    #[false, true, false, true, false, false, false, false, false, false, false],
    #[true, true, true, false, true, true, true, false, true, false, true],
    #[false, false, false, true, false, true, false, false, false, false, false],
    #[true, true, false, true, true, false, true, false, true, false, true],
    #[true, true, false, true, false, true, false, true, true, false, true],
    #[false, false, false, false, false, false, true, false, true, false, false],
    #[true, true, false, true, false, true, true, true, false, true, true],
    #[false, false, false, false, false, false, false, false, true, false, true],
    #[true, true, false, true, false, true, true, false, true, true, false]]

private theorem k11t7p23_adjacency_row_0 : ∀ j : Fin 11,
    k11t7p23.graph.Adj 0 j ↔ adjacencyTableLookup k11t7p23_adjacencyTable 0 j.val = true := by decide

private theorem k11t7p23_adjacency_row_1 : ∀ j : Fin 11,
    k11t7p23.graph.Adj 1 j ↔ adjacencyTableLookup k11t7p23_adjacencyTable 1 j.val = true := by decide

private theorem k11t7p23_adjacency_row_2 : ∀ j : Fin 11,
    k11t7p23.graph.Adj 2 j ↔ adjacencyTableLookup k11t7p23_adjacencyTable 2 j.val = true := by decide

private theorem k11t7p23_adjacency_row_3 : ∀ j : Fin 11,
    k11t7p23.graph.Adj 3 j ↔ adjacencyTableLookup k11t7p23_adjacencyTable 3 j.val = true := by decide

private theorem k11t7p23_adjacency_row_4 : ∀ j : Fin 11,
    k11t7p23.graph.Adj 4 j ↔ adjacencyTableLookup k11t7p23_adjacencyTable 4 j.val = true := by decide

private theorem k11t7p23_adjacency_row_5 : ∀ j : Fin 11,
    k11t7p23.graph.Adj 5 j ↔ adjacencyTableLookup k11t7p23_adjacencyTable 5 j.val = true := by decide

private theorem k11t7p23_adjacency_row_6 : ∀ j : Fin 11,
    k11t7p23.graph.Adj 6 j ↔ adjacencyTableLookup k11t7p23_adjacencyTable 6 j.val = true := by decide

private theorem k11t7p23_adjacency_row_7 : ∀ j : Fin 11,
    k11t7p23.graph.Adj 7 j ↔ adjacencyTableLookup k11t7p23_adjacencyTable 7 j.val = true := by decide

private theorem k11t7p23_adjacency_row_8 : ∀ j : Fin 11,
    k11t7p23.graph.Adj 8 j ↔ adjacencyTableLookup k11t7p23_adjacencyTable 8 j.val = true := by decide

private theorem k11t7p23_adjacency_row_9 : ∀ j : Fin 11,
    k11t7p23.graph.Adj 9 j ↔ adjacencyTableLookup k11t7p23_adjacencyTable 9 j.val = true := by decide

private theorem k11t7p23_adjacency_row_10 : ∀ j : Fin 11,
    k11t7p23.graph.Adj 10 j ↔ adjacencyTableLookup k11t7p23_adjacencyTable 10 j.val = true := by decide

private theorem k11t7p23_adjacency_eq : ∀ i j : Fin 11,
    k11t7p23.graph.Adj i j ↔ adjacencyTableLookup k11t7p23_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t7p23_adjacency_row_0 j

  · exact k11t7p23_adjacency_row_1 j

  · exact k11t7p23_adjacency_row_2 j

  · exact k11t7p23_adjacency_row_3 j

  · exact k11t7p23_adjacency_row_4 j

  · exact k11t7p23_adjacency_row_5 j

  · exact k11t7p23_adjacency_row_6 j

  · exact k11t7p23_adjacency_row_7 j

  · exact k11t7p23_adjacency_row_8 j

  · exact k11t7p23_adjacency_row_9 j

  · exact k11t7p23_adjacency_row_10 j

private def k11t7p23_tableGraph : SimpleGraph (Fin 11) :=
  adjacencyTableGraph k11t7p23.graph k11t7p23_adjacencyTable k11t7p23_adjacency_eq

private instance k11t7p23_tableGraph_decidableAdj :
    DecidableRel k11t7p23_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t7p23_adjacencyTable i.val j.val = true))

private theorem k11t7p23_tableGraph_eq : k11t7p23_tableGraph = k11t7p23.graph :=
  adjacencyTableGraph_eq k11t7p23.graph k11t7p23_adjacencyTable k11t7p23_adjacency_eq

private def k11t7p23_state_0 : ForbiddenMatrix 11 :=
  fun i j => ((#[#[∅, ∅, {1, 2, 3}, ∅, Finset.Icc 1 4, ∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅],
    #[∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 5, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 6, ∅, Finset.Icc 1 6, ∅],
    #[∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 6, Finset.Icc 1 5, ∅, ∅, ∅, Finset.Icc 1 8, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 6, Finset.Icc 1 5, ∅, Finset.Icc 1 8, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t7p23_decode_entry_0 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t7p23_decode_entry_1 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p23_decode_entry_2 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p23_decode_entry_3 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p23_decode_entry_4 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p23_decode_entry_5 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p23_decode_entry_6 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p23_decode_entry_7 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p23_decode_entry_8 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p23_decode_entry_9 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p23_decode_entry_10 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p23_decode_entry_11 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p23_decode_entry_12 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p23_decode_entry_13 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p23_decode_entry_14 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p23_decode_entry_15 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p23_decode_entry_16 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p23_decode_entry_17 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t7p23_decode_entry_18 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t7p23_decode_entry_19 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p23_decode_entry_20 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p23_decode_entry_21 : decode 12 508 = Finset.Icc 2 8 := by decide

private theorem k11t7p23_decode_entry_22 : decode 12 62 = Finset.Icc 1 5 := by decide

private def k11t7p23_mask_entries_0 : List (TemplateData (Fin 11) × ℕ) := [(⟨0, 2, [[3, 4, 5], [6, 7, 8]], [], [1], 1, 3⟩, 14), (⟨0, 4, [[6, 7, 8]], [], [3, 2, 1], 1, 4⟩, 30), (⟨0, 7, [[1, 2, 3, 4, 5]], [], [6], 1, 4⟩, 30), (⟨0, 9, [[1, 2, 3, 4, 5]], [], [8], 1, 4⟩, 30), (⟨1, 2, [[6, 7, 8]], [], [3, 4, 5], 1, 4⟩, 30), (⟨1, 4, [[6, 7, 8]], [3, 2], [5], 1, 4⟩, 30), (⟨1, 7, [], [5, 4, 3, 2], [6], 1, 5⟩, 62), (⟨1, 9, [], [5, 4, 3, 2], [8], 1, 5⟩, 62), (⟨2, 3, [[6, 7, 8]], [1], [4, 5], 1, 4⟩, 30), (⟨2, 4, [[6, 7, 8]], [1], [3], 1, 5⟩, 62), (⟨2, 5, [[6, 7, 8]], [1], [4, 3], 1, 4⟩, 30), (⟨2, 7, [[3, 4, 5]], [1], [6], 1, 5⟩, 62), (⟨2, 9, [[3, 4, 5]], [1], [8], 1, 5⟩, 62), (⟨3, 4, [[6, 7, 8]], [1, 2], [5], 1, 4⟩, 30), (⟨3, 7, [[8, 9, 10]], [1, 2], [6], 1, 4⟩, 30), (⟨3, 9, [], [1, 2], [8, 7, 6], 1, 5⟩, 62), (⟨4, 5, [[6, 7, 8]], [1, 2, 3], [], 1, 4⟩, 30), (⟨4, 7, [], [1, 2, 3], [6], 1, 6⟩, 126), (⟨4, 9, [], [1, 2, 3], [8], 1, 6⟩, 126), (⟨5, 7, [], [1, 2, 3, 4], [6], 1, 5⟩, 62), (⟨5, 9, [], [1, 2, 3, 4], [8], 1, 5⟩, 62), (⟨7, 9, [], [6], [8], 2, 8⟩, 508), (⟨7, 9, [[1, 2, 3]], [6], [8], 1, 5⟩, 62)]

private theorem k11t7p23_decode_entries_0 : ∀ Tb ∈ k11t7p23_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t7p23_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t7p23_decode_entry_0, k11t7p23_decode_entry_1, k11t7p23_decode_entry_2, k11t7p23_decode_entry_3, k11t7p23_decode_entry_4, k11t7p23_decode_entry_5, k11t7p23_decode_entry_6, k11t7p23_decode_entry_7, k11t7p23_decode_entry_8, k11t7p23_decode_entry_9, k11t7p23_decode_entry_10, k11t7p23_decode_entry_11, k11t7p23_decode_entry_12, k11t7p23_decode_entry_13, k11t7p23_decode_entry_14, k11t7p23_decode_entry_15, k11t7p23_decode_entry_16, k11t7p23_decode_entry_17, k11t7p23_decode_entry_18, k11t7p23_decode_entry_19, k11t7p23_decode_entry_20, k11t7p23_decode_entry_21, k11t7p23_decode_entry_22⟩

private def k11t7p23_mask_block_0 : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 0, 14, 0, 30, 0, 0, 30, 0, 30, 0],
    #[0, 0, 30, 0, 30, 0, 0, 62, 0, 62, 0],
    #[14, 30, 0, 30, 62, 30, 0, 62, 0, 62, 0],
    #[0, 0, 30, 0, 30, 0, 0, 30, 0, 62, 0],
    #[30, 30, 62, 30, 0, 30, 0, 126, 0, 126, 0],
    #[0, 0, 30, 0, 30, 0, 0, 62, 0, 62, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[30, 62, 62, 30, 126, 62, 0, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[30, 62, 62, 62, 126, 62, 0, 510, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t7p23_mask_block_0_eq_row_0 : ∀ j : Fin 11, (templateMaskMatrix k11t7p23_mask_entries_0) 0 j = k11t7p23_mask_block_0 0 j := by decide

private theorem k11t7p23_mask_block_0_eq_row_1 : ∀ j : Fin 11, (templateMaskMatrix k11t7p23_mask_entries_0) 1 j = k11t7p23_mask_block_0 1 j := by decide

private theorem k11t7p23_mask_block_0_eq_row_2 : ∀ j : Fin 11, (templateMaskMatrix k11t7p23_mask_entries_0) 2 j = k11t7p23_mask_block_0 2 j := by decide

private theorem k11t7p23_mask_block_0_eq_row_3 : ∀ j : Fin 11, (templateMaskMatrix k11t7p23_mask_entries_0) 3 j = k11t7p23_mask_block_0 3 j := by decide

private theorem k11t7p23_mask_block_0_eq_row_4 : ∀ j : Fin 11, (templateMaskMatrix k11t7p23_mask_entries_0) 4 j = k11t7p23_mask_block_0 4 j := by decide

private theorem k11t7p23_mask_block_0_eq_row_5 : ∀ j : Fin 11, (templateMaskMatrix k11t7p23_mask_entries_0) 5 j = k11t7p23_mask_block_0 5 j := by decide

private theorem k11t7p23_mask_block_0_eq_row_6 : ∀ j : Fin 11, (templateMaskMatrix k11t7p23_mask_entries_0) 6 j = k11t7p23_mask_block_0 6 j := by decide

private theorem k11t7p23_mask_block_0_eq_row_7 : ∀ j : Fin 11, (templateMaskMatrix k11t7p23_mask_entries_0) 7 j = k11t7p23_mask_block_0 7 j := by decide

private theorem k11t7p23_mask_block_0_eq_row_8 : ∀ j : Fin 11, (templateMaskMatrix k11t7p23_mask_entries_0) 8 j = k11t7p23_mask_block_0 8 j := by decide

private theorem k11t7p23_mask_block_0_eq_row_9 : ∀ j : Fin 11, (templateMaskMatrix k11t7p23_mask_entries_0) 9 j = k11t7p23_mask_block_0 9 j := by decide

private theorem k11t7p23_mask_block_0_eq_row_10 : ∀ j : Fin 11, (templateMaskMatrix k11t7p23_mask_entries_0) 10 j = k11t7p23_mask_block_0 10 j := by decide

private theorem k11t7p23_mask_block_0_eq : (templateMaskMatrix k11t7p23_mask_entries_0) = k11t7p23_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t7p23_mask_block_0_eq_row_0 j

  · exact k11t7p23_mask_block_0_eq_row_1 j

  · exact k11t7p23_mask_block_0_eq_row_2 j

  · exact k11t7p23_mask_block_0_eq_row_3 j

  · exact k11t7p23_mask_block_0_eq_row_4 j

  · exact k11t7p23_mask_block_0_eq_row_5 j

  · exact k11t7p23_mask_block_0_eq_row_6 j

  · exact k11t7p23_mask_block_0_eq_row_7 j

  · exact k11t7p23_mask_block_0_eq_row_8 j

  · exact k11t7p23_mask_block_0_eq_row_9 j

  · exact k11t7p23_mask_block_0_eq_row_10 j

private def k11t7p23_mask_entries : List (TemplateData (Fin 11) × ℕ) := k11t7p23_mask_entries_0

private theorem k11t7p23_decode_entries : ∀ Tb ∈ k11t7p23_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t7p23_decode_entries_0

private theorem k11t7p23_mask_entries_map : k11t7p23_mask_entries.map Prod.fst = k11t7p23.templates := by rfl

private def k11t7p23_template_mask : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 0, 14, 0, 30, 0, 0, 30, 0, 30, 0],
    #[0, 0, 30, 0, 30, 0, 0, 62, 0, 62, 0],
    #[14, 30, 0, 30, 62, 30, 0, 62, 0, 62, 0],
    #[0, 0, 30, 0, 30, 0, 0, 30, 0, 62, 0],
    #[30, 30, 62, 30, 0, 30, 0, 126, 0, 126, 0],
    #[0, 0, 30, 0, 30, 0, 0, 62, 0, 62, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[30, 62, 62, 30, 126, 62, 0, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[30, 62, 62, 62, 126, 62, 0, 510, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t7p23_mask_merged_eq_row_0 : ∀ j : Fin 11, (fun i j => k11t7p23_mask_block_0 i j) 0 j = k11t7p23_template_mask 0 j := by decide

private theorem k11t7p23_mask_merged_eq_row_1 : ∀ j : Fin 11, (fun i j => k11t7p23_mask_block_0 i j) 1 j = k11t7p23_template_mask 1 j := by decide

private theorem k11t7p23_mask_merged_eq_row_2 : ∀ j : Fin 11, (fun i j => k11t7p23_mask_block_0 i j) 2 j = k11t7p23_template_mask 2 j := by decide

private theorem k11t7p23_mask_merged_eq_row_3 : ∀ j : Fin 11, (fun i j => k11t7p23_mask_block_0 i j) 3 j = k11t7p23_template_mask 3 j := by decide

private theorem k11t7p23_mask_merged_eq_row_4 : ∀ j : Fin 11, (fun i j => k11t7p23_mask_block_0 i j) 4 j = k11t7p23_template_mask 4 j := by decide

private theorem k11t7p23_mask_merged_eq_row_5 : ∀ j : Fin 11, (fun i j => k11t7p23_mask_block_0 i j) 5 j = k11t7p23_template_mask 5 j := by decide

private theorem k11t7p23_mask_merged_eq_row_6 : ∀ j : Fin 11, (fun i j => k11t7p23_mask_block_0 i j) 6 j = k11t7p23_template_mask 6 j := by decide

private theorem k11t7p23_mask_merged_eq_row_7 : ∀ j : Fin 11, (fun i j => k11t7p23_mask_block_0 i j) 7 j = k11t7p23_template_mask 7 j := by decide

private theorem k11t7p23_mask_merged_eq_row_8 : ∀ j : Fin 11, (fun i j => k11t7p23_mask_block_0 i j) 8 j = k11t7p23_template_mask 8 j := by decide

private theorem k11t7p23_mask_merged_eq_row_9 : ∀ j : Fin 11, (fun i j => k11t7p23_mask_block_0 i j) 9 j = k11t7p23_template_mask 9 j := by decide

private theorem k11t7p23_mask_merged_eq_row_10 : ∀ j : Fin 11, (fun i j => k11t7p23_mask_block_0 i j) 10 j = k11t7p23_template_mask 10 j := by decide

private theorem k11t7p23_mask_merged_eq : (fun i j => k11t7p23_mask_block_0 i j) = k11t7p23_template_mask := by
  funext i j
  fin_cases i

  · exact k11t7p23_mask_merged_eq_row_0 j

  · exact k11t7p23_mask_merged_eq_row_1 j

  · exact k11t7p23_mask_merged_eq_row_2 j

  · exact k11t7p23_mask_merged_eq_row_3 j

  · exact k11t7p23_mask_merged_eq_row_4 j

  · exact k11t7p23_mask_merged_eq_row_5 j

  · exact k11t7p23_mask_merged_eq_row_6 j

  · exact k11t7p23_mask_merged_eq_row_7 j

  · exact k11t7p23_mask_merged_eq_row_8 j

  · exact k11t7p23_mask_merged_eq_row_9 j

  · exact k11t7p23_mask_merged_eq_row_10 j

private theorem k11t7p23_template_mask_eq : templateMaskMatrix k11t7p23_mask_entries = k11t7p23_template_mask := by
  funext i j
  change templateMaskMatrix (k11t7p23_mask_entries_0) i j = _
  simp only [k11t7p23_mask_block_0_eq]
  exact congrFun (congrFun k11t7p23_mask_merged_eq i) j

private theorem k11t7p23_initial_decoded_eq_row_0 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) 0 j = k11t7p23_state_0 0 j := by decide

private theorem k11t7p23_initial_decoded_eq_row_1 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) 1 j = k11t7p23_state_0 1 j := by decide

private theorem k11t7p23_initial_decoded_eq_row_2 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) 2 j = k11t7p23_state_0 2 j := by decide

private theorem k11t7p23_initial_decoded_eq_row_3 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) 3 j = k11t7p23_state_0 3 j := by decide

private theorem k11t7p23_initial_decoded_eq_row_4 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) 4 j = k11t7p23_state_0 4 j := by decide

private theorem k11t7p23_initial_decoded_eq_row_5 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) 5 j = k11t7p23_state_0 5 j := by decide

private theorem k11t7p23_initial_decoded_eq_row_6 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) 6 j = k11t7p23_state_0 6 j := by decide

private theorem k11t7p23_initial_decoded_eq_row_7 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) 7 j = k11t7p23_state_0 7 j := by decide

private theorem k11t7p23_initial_decoded_eq_row_8 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) 8 j = k11t7p23_state_0 8 j := by decide

private theorem k11t7p23_initial_decoded_eq_row_9 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) 9 j = k11t7p23_state_0 9 j := by decide

private theorem k11t7p23_initial_decoded_eq_row_10 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) 10 j = k11t7p23_state_0 10 j := by decide

private theorem k11t7p23_initial_decoded_eq : (fun i j => decode 12 (k11t7p23_template_mask i j) ∪ requiredMatrix 11 k11t7p23.required i j) = k11t7p23_state_0 := by
  funext i j
  fin_cases i

  · exact k11t7p23_initial_decoded_eq_row_0 j

  · exact k11t7p23_initial_decoded_eq_row_1 j

  · exact k11t7p23_initial_decoded_eq_row_2 j

  · exact k11t7p23_initial_decoded_eq_row_3 j

  · exact k11t7p23_initial_decoded_eq_row_4 j

  · exact k11t7p23_initial_decoded_eq_row_5 j

  · exact k11t7p23_initial_decoded_eq_row_6 j

  · exact k11t7p23_initial_decoded_eq_row_7 j

  · exact k11t7p23_initial_decoded_eq_row_8 j

  · exact k11t7p23_initial_decoded_eq_row_9 j

  · exact k11t7p23_initial_decoded_eq_row_10 j

private theorem k11t7p23_initial_eq : k11t7p23.initialMatrix 11 = k11t7p23_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t7p23_mask_entries k11t7p23_decode_entries
  rw [k11t7p23_mask_entries_map, k11t7p23_template_mask_eq] at h
  funext i j
  change templateMatrix k11t7p23.templates i j ∪ requiredMatrix 11 k11t7p23.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t7p23_initial_decoded_eq i) j

private theorem k11t7p23_closure_0 : ClosureCheck k11t7p23.graph k11t7p23_state_0 11 7 [] := by trivial

private theorem k11t7p23_matrix_eq : k11t7p23.matrix 11 = k11t7p23_state_0 := by
  change closureMatrix (k11t7p23.initialMatrix 11) _ = _
  rw [k11t7p23_initial_eq]
  change closureMatrix k11t7p23_state_0 [] = _
  rfl

private theorem k11t7p23_part_0 : k11t7p23.chains.flatten = List.finRange _ := by decide

private theorem k11t7p23_part_1 : k11t7p23.chains.map List.length = ([[], [1, 1], [1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t7p23_part_2 : k11t7p23.chains.map (fun l => l.map (fun i => decide (i ∈ k11t7p23.clique))) = ([[], [1, 1], [1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k11t7p23_templates_item_0 : (⟨0, 2, [[3, 4, 5], [6, 7, 8]], [], [1], 1, 3⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_1 : (⟨0, 4, [[6, 7, 8]], [], [3, 2, 1], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_2 : (⟨0, 7, [[1, 2, 3, 4, 5]], [], [6], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_3 : (⟨0, 9, [[1, 2, 3, 4, 5]], [], [8], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_4 : (⟨1, 2, [[6, 7, 8]], [], [3, 4, 5], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_5 : (⟨1, 4, [[6, 7, 8]], [3, 2], [5], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_6 : (⟨1, 7, [], [5, 4, 3, 2], [6], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_7 : (⟨1, 9, [], [5, 4, 3, 2], [8], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_8 : (⟨2, 3, [[6, 7, 8]], [1], [4, 5], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_9 : (⟨2, 4, [[6, 7, 8]], [1], [3], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_10 : (⟨2, 5, [[6, 7, 8]], [1], [4, 3], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_11 : (⟨2, 7, [[3, 4, 5]], [1], [6], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_12 : (⟨2, 9, [[3, 4, 5]], [1], [8], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_13 : (⟨3, 4, [[6, 7, 8]], [1, 2], [5], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_14 : (⟨3, 7, [[8, 9, 10]], [1, 2], [6], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_15 : (⟨3, 9, [], [1, 2], [8, 7, 6], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_16 : (⟨4, 5, [[6, 7, 8]], [1, 2, 3], [], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_17 : (⟨4, 7, [], [1, 2, 3], [6], 1, 6⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_18 : (⟨4, 9, [], [1, 2, 3], [8], 1, 6⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_19 : (⟨5, 7, [], [1, 2, 3, 4], [6], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_20 : (⟨5, 9, [], [1, 2, 3, 4], [8], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_21 : (⟨7, 9, [], [6], [8], 2, 8⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_item_22 : (⟨7, 9, [[1, 2, 3]], [6], [8], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p23_tableGraph_eq]
  decide

private theorem k11t7p23_templates_fast_block_0_check : ∀ T ∈ k11t7p23_mask_entries_0.map Prod.fst, T.Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t7p23_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t7p23_templates_item_0, k11t7p23_templates_item_1, k11t7p23_templates_item_2, k11t7p23_templates_item_3, k11t7p23_templates_item_4, k11t7p23_templates_item_5, k11t7p23_templates_item_6, k11t7p23_templates_item_7, k11t7p23_templates_item_8, k11t7p23_templates_item_9, k11t7p23_templates_item_10, k11t7p23_templates_item_11, k11t7p23_templates_item_12, k11t7p23_templates_item_13, k11t7p23_templates_item_14, k11t7p23_templates_item_15, k11t7p23_templates_item_16, k11t7p23_templates_item_17, k11t7p23_templates_item_18, k11t7p23_templates_item_19, k11t7p23_templates_item_20, k11t7p23_templates_item_21, k11t7p23_templates_item_22⟩

private theorem k11t7p23_part_3 : ∀ T ∈ k11t7p23.templates, T.Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t7p23_mask_entries_0.map Prod.fst), T.Check k11t7p23.graph k11t7p23.clique 11 (patternAmount ([[], [1, 1], [1, 1]] : List (List ℕ))) (([[], [1, 1], [1, 1]] : List (List ℕ)).map List.length).sum
  exact k11t7p23_templates_fast_block_0_check

private theorem k11t7p23_part_4 : ∀ p ∈ k11t7p23.required, p.Check k11t7p23.graph 11 := by decide

private theorem k11t7p23_part_5 : ClosureCheck k11t7p23.graph (k11t7p23.initialMatrix 11) 11 7 k11t7p23.closure := by
  rw [k11t7p23_initial_eq]
  exact k11t7p23_closure_0

private theorem k11t7p23_part_6 : k11t7p23.bad.Check k11t7p23.graph (k11t7p23.matrix 11) 11 7 := by
  rw [k11t7p23_matrix_eq]
  decide

theorem k11t7p23_check : k11t7p23.Check 11 7 [[], [1, 1], [1, 1]] :=
  ⟨k11t7p23_part_0, k11t7p23_part_1, k11t7p23_part_2, k11t7p23_part_3, k11t7p23_part_4, k11t7p23_part_5, k11t7p23_part_6⟩
def k11t7p24 : LayoutCertificate 11 where
  chains := [[0, 1, 2], [3, 4, 5], [6, 7, 8, 9, 10]]
  clique := {0, 2, 3, 5, 6, 8, 10}
  templates := [⟨0, 1, [[3, 4, 5], [6, 7, 8]], [], [2], 1, 3⟩,
    ⟨0, 4, [[6, 7, 8]], [2, 1], [3], 1, 4⟩,
    ⟨0, 7, [[3, 4, 5]], [2, 1], [6], 1, 4⟩,
    ⟨0, 9, [[3, 4, 5]], [2, 1], [8], 1, 4⟩,
    ⟨1, 2, [[3, 4, 5], [6, 7, 8]], [0], [], 1, 3⟩,
    ⟨1, 3, [[6, 7, 8]], [0], [4, 5], 1, 4⟩,
    ⟨1, 4, [[6, 7, 8]], [0], [3], 1, 5⟩,
    ⟨1, 5, [[6, 7, 8]], [0], [4, 3], 1, 4⟩,
    ⟨1, 7, [[3, 4, 5]], [0], [6], 1, 5⟩,
    ⟨1, 9, [[3, 4, 5]], [0], [8], 1, 5⟩,
    ⟨2, 4, [[6, 7, 8]], [0, 1], [3], 1, 4⟩,
    ⟨2, 7, [[3, 4, 5]], [0, 1], [6], 1, 4⟩,
    ⟨2, 9, [[3, 4, 5]], [0, 1], [8], 1, 4⟩,
    ⟨3, 4, [[0, 1, 2], [6, 7, 8]], [], [5], 1, 3⟩,
    ⟨3, 7, [[0, 1, 2]], [5, 4], [6], 1, 4⟩,
    ⟨3, 9, [[0, 1, 2]], [5, 4], [8], 1, 4⟩,
    ⟨4, 5, [[0, 1, 2], [6, 7, 8]], [3], [], 1, 3⟩,
    ⟨4, 7, [], [3], [6], 2, 8⟩,
    ⟨4, 7, [[0, 1, 2]], [3], [6], 1, 5⟩,
    ⟨4, 9, [], [3], [8], 2, 8⟩,
    ⟨4, 9, [[0, 1, 2]], [3], [8], 1, 5⟩,
    ⟨5, 7, [[0, 1, 2]], [3, 4], [6], 1, 4⟩,
    ⟨5, 9, [[0, 1, 2]], [3, 4], [8], 1, 4⟩,
    ⟨7, 9, [], [6], [8], 2, 8⟩,
    ⟨7, 9, [[0, 1, 2]], [6], [8], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 0), (1, 2), (4, 3), (7, 3), (9, 3)}⟩


private def k11t7p24_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, true, false, true, true, false, true, false, true],
    #[true, false, true, false, false, false, false, false, false, false, false],
    #[true, true, false, true, false, true, true, false, true, false, true],
    #[true, false, true, false, true, true, true, false, true, false, true],
    #[false, false, false, true, false, true, false, false, false, false, false],
    #[true, false, true, true, true, false, true, false, true, false, true],
    #[true, false, true, true, false, true, false, true, true, false, true],
    #[false, false, false, false, false, false, true, false, true, false, false],
    #[true, false, true, true, false, true, true, true, false, true, true],
    #[false, false, false, false, false, false, false, false, true, false, true],
    #[true, false, true, true, false, true, true, false, true, true, false]]

private theorem k11t7p24_adjacency_row_0 : ∀ j : Fin 11,
    k11t7p24.graph.Adj 0 j ↔ adjacencyTableLookup k11t7p24_adjacencyTable 0 j.val = true := by decide

private theorem k11t7p24_adjacency_row_1 : ∀ j : Fin 11,
    k11t7p24.graph.Adj 1 j ↔ adjacencyTableLookup k11t7p24_adjacencyTable 1 j.val = true := by decide

private theorem k11t7p24_adjacency_row_2 : ∀ j : Fin 11,
    k11t7p24.graph.Adj 2 j ↔ adjacencyTableLookup k11t7p24_adjacencyTable 2 j.val = true := by decide

private theorem k11t7p24_adjacency_row_3 : ∀ j : Fin 11,
    k11t7p24.graph.Adj 3 j ↔ adjacencyTableLookup k11t7p24_adjacencyTable 3 j.val = true := by decide

private theorem k11t7p24_adjacency_row_4 : ∀ j : Fin 11,
    k11t7p24.graph.Adj 4 j ↔ adjacencyTableLookup k11t7p24_adjacencyTable 4 j.val = true := by decide

private theorem k11t7p24_adjacency_row_5 : ∀ j : Fin 11,
    k11t7p24.graph.Adj 5 j ↔ adjacencyTableLookup k11t7p24_adjacencyTable 5 j.val = true := by decide

private theorem k11t7p24_adjacency_row_6 : ∀ j : Fin 11,
    k11t7p24.graph.Adj 6 j ↔ adjacencyTableLookup k11t7p24_adjacencyTable 6 j.val = true := by decide

private theorem k11t7p24_adjacency_row_7 : ∀ j : Fin 11,
    k11t7p24.graph.Adj 7 j ↔ adjacencyTableLookup k11t7p24_adjacencyTable 7 j.val = true := by decide

private theorem k11t7p24_adjacency_row_8 : ∀ j : Fin 11,
    k11t7p24.graph.Adj 8 j ↔ adjacencyTableLookup k11t7p24_adjacencyTable 8 j.val = true := by decide

private theorem k11t7p24_adjacency_row_9 : ∀ j : Fin 11,
    k11t7p24.graph.Adj 9 j ↔ adjacencyTableLookup k11t7p24_adjacencyTable 9 j.val = true := by decide

private theorem k11t7p24_adjacency_row_10 : ∀ j : Fin 11,
    k11t7p24.graph.Adj 10 j ↔ adjacencyTableLookup k11t7p24_adjacencyTable 10 j.val = true := by decide

private theorem k11t7p24_adjacency_eq : ∀ i j : Fin 11,
    k11t7p24.graph.Adj i j ↔ adjacencyTableLookup k11t7p24_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t7p24_adjacency_row_0 j

  · exact k11t7p24_adjacency_row_1 j

  · exact k11t7p24_adjacency_row_2 j

  · exact k11t7p24_adjacency_row_3 j

  · exact k11t7p24_adjacency_row_4 j

  · exact k11t7p24_adjacency_row_5 j

  · exact k11t7p24_adjacency_row_6 j

  · exact k11t7p24_adjacency_row_7 j

  · exact k11t7p24_adjacency_row_8 j

  · exact k11t7p24_adjacency_row_9 j

  · exact k11t7p24_adjacency_row_10 j

private def k11t7p24_tableGraph : SimpleGraph (Fin 11) :=
  adjacencyTableGraph k11t7p24.graph k11t7p24_adjacencyTable k11t7p24_adjacency_eq

private instance k11t7p24_tableGraph_decidableAdj :
    DecidableRel k11t7p24_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t7p24_adjacencyTable i.val j.val = true))

private theorem k11t7p24_tableGraph_eq : k11t7p24_tableGraph = k11t7p24.graph :=
  adjacencyTableGraph_eq k11t7p24.graph k11t7p24_adjacencyTable k11t7p24_adjacency_eq

private def k11t7p24_state_0 : ForbiddenMatrix 11 :=
  fun i j => ((#[#[∅, {1, 2, 3}, ∅, ∅, Finset.Icc 1 4, ∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[{1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅],
    #[∅, {1, 2, 3}, ∅, ∅, Finset.Icc 1 4, ∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[∅, Finset.Icc 1 4, ∅, ∅, {1, 2, 3}, ∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅, Finset.Icc 1 8, ∅, Finset.Icc 1 8, ∅],
    #[∅, Finset.Icc 1 4, ∅, ∅, {1, 2, 3}, ∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 8, Finset.Icc 1 4, ∅, ∅, ∅, Finset.Icc 1 8, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 8, Finset.Icc 1 4, ∅, Finset.Icc 1 8, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t7p24_decode_entry_0 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t7p24_decode_entry_1 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_2 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_3 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_4 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t7p24_decode_entry_5 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_6 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p24_decode_entry_7 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_8 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p24_decode_entry_9 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p24_decode_entry_10 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_11 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_12 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_13 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t7p24_decode_entry_14 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_15 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_16 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t7p24_decode_entry_17 : decode 12 508 = Finset.Icc 2 8 := by decide

private theorem k11t7p24_decode_entry_18 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p24_decode_entry_19 : decode 12 508 = Finset.Icc 2 8 := by decide

private theorem k11t7p24_decode_entry_20 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t7p24_decode_entry_21 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_22 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t7p24_decode_entry_23 : decode 12 508 = Finset.Icc 2 8 := by decide

private theorem k11t7p24_decode_entry_24 : decode 12 62 = Finset.Icc 1 5 := by decide

private def k11t7p24_mask_entries_0 : List (TemplateData (Fin 11) × ℕ) := [(⟨0, 1, [[3, 4, 5], [6, 7, 8]], [], [2], 1, 3⟩, 14), (⟨0, 4, [[6, 7, 8]], [2, 1], [3], 1, 4⟩, 30), (⟨0, 7, [[3, 4, 5]], [2, 1], [6], 1, 4⟩, 30), (⟨0, 9, [[3, 4, 5]], [2, 1], [8], 1, 4⟩, 30), (⟨1, 2, [[3, 4, 5], [6, 7, 8]], [0], [], 1, 3⟩, 14), (⟨1, 3, [[6, 7, 8]], [0], [4, 5], 1, 4⟩, 30), (⟨1, 4, [[6, 7, 8]], [0], [3], 1, 5⟩, 62), (⟨1, 5, [[6, 7, 8]], [0], [4, 3], 1, 4⟩, 30), (⟨1, 7, [[3, 4, 5]], [0], [6], 1, 5⟩, 62), (⟨1, 9, [[3, 4, 5]], [0], [8], 1, 5⟩, 62), (⟨2, 4, [[6, 7, 8]], [0, 1], [3], 1, 4⟩, 30), (⟨2, 7, [[3, 4, 5]], [0, 1], [6], 1, 4⟩, 30), (⟨2, 9, [[3, 4, 5]], [0, 1], [8], 1, 4⟩, 30), (⟨3, 4, [[0, 1, 2], [6, 7, 8]], [], [5], 1, 3⟩, 14), (⟨3, 7, [[0, 1, 2]], [5, 4], [6], 1, 4⟩, 30), (⟨3, 9, [[0, 1, 2]], [5, 4], [8], 1, 4⟩, 30), (⟨4, 5, [[0, 1, 2], [6, 7, 8]], [3], [], 1, 3⟩, 14), (⟨4, 7, [], [3], [6], 2, 8⟩, 508), (⟨4, 7, [[0, 1, 2]], [3], [6], 1, 5⟩, 62), (⟨4, 9, [], [3], [8], 2, 8⟩, 508), (⟨4, 9, [[0, 1, 2]], [3], [8], 1, 5⟩, 62), (⟨5, 7, [[0, 1, 2]], [3, 4], [6], 1, 4⟩, 30), (⟨5, 9, [[0, 1, 2]], [3, 4], [8], 1, 4⟩, 30), (⟨7, 9, [], [6], [8], 2, 8⟩, 508), (⟨7, 9, [[0, 1, 2]], [6], [8], 1, 5⟩, 62)]

private theorem k11t7p24_decode_entries_0 : ∀ Tb ∈ k11t7p24_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t7p24_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t7p24_decode_entry_0, k11t7p24_decode_entry_1, k11t7p24_decode_entry_2, k11t7p24_decode_entry_3, k11t7p24_decode_entry_4, k11t7p24_decode_entry_5, k11t7p24_decode_entry_6, k11t7p24_decode_entry_7, k11t7p24_decode_entry_8, k11t7p24_decode_entry_9, k11t7p24_decode_entry_10, k11t7p24_decode_entry_11, k11t7p24_decode_entry_12, k11t7p24_decode_entry_13, k11t7p24_decode_entry_14, k11t7p24_decode_entry_15, k11t7p24_decode_entry_16, k11t7p24_decode_entry_17, k11t7p24_decode_entry_18, k11t7p24_decode_entry_19, k11t7p24_decode_entry_20, k11t7p24_decode_entry_21, k11t7p24_decode_entry_22, k11t7p24_decode_entry_23, k11t7p24_decode_entry_24⟩

private def k11t7p24_mask_block_0 : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 14, 0, 0, 30, 0, 0, 30, 0, 30, 0],
    #[14, 0, 14, 30, 62, 30, 0, 62, 0, 62, 0],
    #[0, 14, 0, 0, 30, 0, 0, 30, 0, 30, 0],
    #[0, 30, 0, 0, 14, 0, 0, 30, 0, 30, 0],
    #[30, 62, 30, 14, 0, 14, 0, 510, 0, 510, 0],
    #[0, 30, 0, 0, 14, 0, 0, 30, 0, 30, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[30, 62, 30, 30, 510, 30, 0, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[30, 62, 30, 30, 510, 30, 0, 510, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t7p24_mask_block_0_eq_row_0 : ∀ j : Fin 11, (templateMaskMatrix k11t7p24_mask_entries_0) 0 j = k11t7p24_mask_block_0 0 j := by decide

private theorem k11t7p24_mask_block_0_eq_row_1 : ∀ j : Fin 11, (templateMaskMatrix k11t7p24_mask_entries_0) 1 j = k11t7p24_mask_block_0 1 j := by decide

private theorem k11t7p24_mask_block_0_eq_row_2 : ∀ j : Fin 11, (templateMaskMatrix k11t7p24_mask_entries_0) 2 j = k11t7p24_mask_block_0 2 j := by decide

private theorem k11t7p24_mask_block_0_eq_row_3 : ∀ j : Fin 11, (templateMaskMatrix k11t7p24_mask_entries_0) 3 j = k11t7p24_mask_block_0 3 j := by decide

private theorem k11t7p24_mask_block_0_eq_row_4 : ∀ j : Fin 11, (templateMaskMatrix k11t7p24_mask_entries_0) 4 j = k11t7p24_mask_block_0 4 j := by decide

private theorem k11t7p24_mask_block_0_eq_row_5 : ∀ j : Fin 11, (templateMaskMatrix k11t7p24_mask_entries_0) 5 j = k11t7p24_mask_block_0 5 j := by decide

private theorem k11t7p24_mask_block_0_eq_row_6 : ∀ j : Fin 11, (templateMaskMatrix k11t7p24_mask_entries_0) 6 j = k11t7p24_mask_block_0 6 j := by decide

private theorem k11t7p24_mask_block_0_eq_row_7 : ∀ j : Fin 11, (templateMaskMatrix k11t7p24_mask_entries_0) 7 j = k11t7p24_mask_block_0 7 j := by decide

private theorem k11t7p24_mask_block_0_eq_row_8 : ∀ j : Fin 11, (templateMaskMatrix k11t7p24_mask_entries_0) 8 j = k11t7p24_mask_block_0 8 j := by decide

private theorem k11t7p24_mask_block_0_eq_row_9 : ∀ j : Fin 11, (templateMaskMatrix k11t7p24_mask_entries_0) 9 j = k11t7p24_mask_block_0 9 j := by decide

private theorem k11t7p24_mask_block_0_eq_row_10 : ∀ j : Fin 11, (templateMaskMatrix k11t7p24_mask_entries_0) 10 j = k11t7p24_mask_block_0 10 j := by decide

private theorem k11t7p24_mask_block_0_eq : (templateMaskMatrix k11t7p24_mask_entries_0) = k11t7p24_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t7p24_mask_block_0_eq_row_0 j

  · exact k11t7p24_mask_block_0_eq_row_1 j

  · exact k11t7p24_mask_block_0_eq_row_2 j

  · exact k11t7p24_mask_block_0_eq_row_3 j

  · exact k11t7p24_mask_block_0_eq_row_4 j

  · exact k11t7p24_mask_block_0_eq_row_5 j

  · exact k11t7p24_mask_block_0_eq_row_6 j

  · exact k11t7p24_mask_block_0_eq_row_7 j

  · exact k11t7p24_mask_block_0_eq_row_8 j

  · exact k11t7p24_mask_block_0_eq_row_9 j

  · exact k11t7p24_mask_block_0_eq_row_10 j

private def k11t7p24_mask_entries : List (TemplateData (Fin 11) × ℕ) := k11t7p24_mask_entries_0

private theorem k11t7p24_decode_entries : ∀ Tb ∈ k11t7p24_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t7p24_decode_entries_0

private theorem k11t7p24_mask_entries_map : k11t7p24_mask_entries.map Prod.fst = k11t7p24.templates := by rfl

private def k11t7p24_template_mask : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 14, 0, 0, 30, 0, 0, 30, 0, 30, 0],
    #[14, 0, 14, 30, 62, 30, 0, 62, 0, 62, 0],
    #[0, 14, 0, 0, 30, 0, 0, 30, 0, 30, 0],
    #[0, 30, 0, 0, 14, 0, 0, 30, 0, 30, 0],
    #[30, 62, 30, 14, 0, 14, 0, 510, 0, 510, 0],
    #[0, 30, 0, 0, 14, 0, 0, 30, 0, 30, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[30, 62, 30, 30, 510, 30, 0, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[30, 62, 30, 30, 510, 30, 0, 510, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t7p24_mask_merged_eq_row_0 : ∀ j : Fin 11, (fun i j => k11t7p24_mask_block_0 i j) 0 j = k11t7p24_template_mask 0 j := by decide

private theorem k11t7p24_mask_merged_eq_row_1 : ∀ j : Fin 11, (fun i j => k11t7p24_mask_block_0 i j) 1 j = k11t7p24_template_mask 1 j := by decide

private theorem k11t7p24_mask_merged_eq_row_2 : ∀ j : Fin 11, (fun i j => k11t7p24_mask_block_0 i j) 2 j = k11t7p24_template_mask 2 j := by decide

private theorem k11t7p24_mask_merged_eq_row_3 : ∀ j : Fin 11, (fun i j => k11t7p24_mask_block_0 i j) 3 j = k11t7p24_template_mask 3 j := by decide

private theorem k11t7p24_mask_merged_eq_row_4 : ∀ j : Fin 11, (fun i j => k11t7p24_mask_block_0 i j) 4 j = k11t7p24_template_mask 4 j := by decide

private theorem k11t7p24_mask_merged_eq_row_5 : ∀ j : Fin 11, (fun i j => k11t7p24_mask_block_0 i j) 5 j = k11t7p24_template_mask 5 j := by decide

private theorem k11t7p24_mask_merged_eq_row_6 : ∀ j : Fin 11, (fun i j => k11t7p24_mask_block_0 i j) 6 j = k11t7p24_template_mask 6 j := by decide

private theorem k11t7p24_mask_merged_eq_row_7 : ∀ j : Fin 11, (fun i j => k11t7p24_mask_block_0 i j) 7 j = k11t7p24_template_mask 7 j := by decide

private theorem k11t7p24_mask_merged_eq_row_8 : ∀ j : Fin 11, (fun i j => k11t7p24_mask_block_0 i j) 8 j = k11t7p24_template_mask 8 j := by decide

private theorem k11t7p24_mask_merged_eq_row_9 : ∀ j : Fin 11, (fun i j => k11t7p24_mask_block_0 i j) 9 j = k11t7p24_template_mask 9 j := by decide

private theorem k11t7p24_mask_merged_eq_row_10 : ∀ j : Fin 11, (fun i j => k11t7p24_mask_block_0 i j) 10 j = k11t7p24_template_mask 10 j := by decide

private theorem k11t7p24_mask_merged_eq : (fun i j => k11t7p24_mask_block_0 i j) = k11t7p24_template_mask := by
  funext i j
  fin_cases i

  · exact k11t7p24_mask_merged_eq_row_0 j

  · exact k11t7p24_mask_merged_eq_row_1 j

  · exact k11t7p24_mask_merged_eq_row_2 j

  · exact k11t7p24_mask_merged_eq_row_3 j

  · exact k11t7p24_mask_merged_eq_row_4 j

  · exact k11t7p24_mask_merged_eq_row_5 j

  · exact k11t7p24_mask_merged_eq_row_6 j

  · exact k11t7p24_mask_merged_eq_row_7 j

  · exact k11t7p24_mask_merged_eq_row_8 j

  · exact k11t7p24_mask_merged_eq_row_9 j

  · exact k11t7p24_mask_merged_eq_row_10 j

private theorem k11t7p24_template_mask_eq : templateMaskMatrix k11t7p24_mask_entries = k11t7p24_template_mask := by
  funext i j
  change templateMaskMatrix (k11t7p24_mask_entries_0) i j = _
  simp only [k11t7p24_mask_block_0_eq]
  exact congrFun (congrFun k11t7p24_mask_merged_eq i) j

private theorem k11t7p24_initial_decoded_eq_row_0 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) 0 j = k11t7p24_state_0 0 j := by decide

private theorem k11t7p24_initial_decoded_eq_row_1 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) 1 j = k11t7p24_state_0 1 j := by decide

private theorem k11t7p24_initial_decoded_eq_row_2 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) 2 j = k11t7p24_state_0 2 j := by decide

private theorem k11t7p24_initial_decoded_eq_row_3 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) 3 j = k11t7p24_state_0 3 j := by decide

private theorem k11t7p24_initial_decoded_eq_row_4 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) 4 j = k11t7p24_state_0 4 j := by decide

private theorem k11t7p24_initial_decoded_eq_row_5 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) 5 j = k11t7p24_state_0 5 j := by decide

private theorem k11t7p24_initial_decoded_eq_row_6 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) 6 j = k11t7p24_state_0 6 j := by decide

private theorem k11t7p24_initial_decoded_eq_row_7 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) 7 j = k11t7p24_state_0 7 j := by decide

private theorem k11t7p24_initial_decoded_eq_row_8 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) 8 j = k11t7p24_state_0 8 j := by decide

private theorem k11t7p24_initial_decoded_eq_row_9 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) 9 j = k11t7p24_state_0 9 j := by decide

private theorem k11t7p24_initial_decoded_eq_row_10 : ∀ j : Fin 11, (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) 10 j = k11t7p24_state_0 10 j := by decide

private theorem k11t7p24_initial_decoded_eq : (fun i j => decode 12 (k11t7p24_template_mask i j) ∪ requiredMatrix 11 k11t7p24.required i j) = k11t7p24_state_0 := by
  funext i j
  fin_cases i

  · exact k11t7p24_initial_decoded_eq_row_0 j

  · exact k11t7p24_initial_decoded_eq_row_1 j

  · exact k11t7p24_initial_decoded_eq_row_2 j

  · exact k11t7p24_initial_decoded_eq_row_3 j

  · exact k11t7p24_initial_decoded_eq_row_4 j

  · exact k11t7p24_initial_decoded_eq_row_5 j

  · exact k11t7p24_initial_decoded_eq_row_6 j

  · exact k11t7p24_initial_decoded_eq_row_7 j

  · exact k11t7p24_initial_decoded_eq_row_8 j

  · exact k11t7p24_initial_decoded_eq_row_9 j

  · exact k11t7p24_initial_decoded_eq_row_10 j

private theorem k11t7p24_initial_eq : k11t7p24.initialMatrix 11 = k11t7p24_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t7p24_mask_entries k11t7p24_decode_entries
  rw [k11t7p24_mask_entries_map, k11t7p24_template_mask_eq] at h
  funext i j
  change templateMatrix k11t7p24.templates i j ∪ requiredMatrix 11 k11t7p24.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t7p24_initial_decoded_eq i) j

private theorem k11t7p24_closure_0 : ClosureCheck k11t7p24.graph k11t7p24_state_0 11 7 [] := by trivial

private theorem k11t7p24_matrix_eq : k11t7p24.matrix 11 = k11t7p24_state_0 := by
  change closureMatrix (k11t7p24.initialMatrix 11) _ = _
  rw [k11t7p24_initial_eq]
  change closureMatrix k11t7p24_state_0 [] = _
  rfl

private theorem k11t7p24_part_0 : k11t7p24.chains.flatten = List.finRange _ := by decide

private theorem k11t7p24_part_1 : k11t7p24.chains.map List.length = ([[1], [1], [1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t7p24_part_2 : k11t7p24.chains.map (fun l => l.map (fun i => decide (i ∈ k11t7p24.clique))) = ([[1], [1], [1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k11t7p24_templates_item_0 : (⟨0, 1, [[3, 4, 5], [6, 7, 8]], [], [2], 1, 3⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_1 : (⟨0, 4, [[6, 7, 8]], [2, 1], [3], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_2 : (⟨0, 7, [[3, 4, 5]], [2, 1], [6], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_3 : (⟨0, 9, [[3, 4, 5]], [2, 1], [8], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_4 : (⟨1, 2, [[3, 4, 5], [6, 7, 8]], [0], [], 1, 3⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_5 : (⟨1, 3, [[6, 7, 8]], [0], [4, 5], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_6 : (⟨1, 4, [[6, 7, 8]], [0], [3], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_7 : (⟨1, 5, [[6, 7, 8]], [0], [4, 3], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_8 : (⟨1, 7, [[3, 4, 5]], [0], [6], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_9 : (⟨1, 9, [[3, 4, 5]], [0], [8], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_10 : (⟨2, 4, [[6, 7, 8]], [0, 1], [3], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_11 : (⟨2, 7, [[3, 4, 5]], [0, 1], [6], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_12 : (⟨2, 9, [[3, 4, 5]], [0, 1], [8], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_13 : (⟨3, 4, [[0, 1, 2], [6, 7, 8]], [], [5], 1, 3⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_14 : (⟨3, 7, [[0, 1, 2]], [5, 4], [6], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_15 : (⟨3, 9, [[0, 1, 2]], [5, 4], [8], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_16 : (⟨4, 5, [[0, 1, 2], [6, 7, 8]], [3], [], 1, 3⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_17 : (⟨4, 7, [], [3], [6], 2, 8⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_18 : (⟨4, 7, [[0, 1, 2]], [3], [6], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_19 : (⟨4, 9, [], [3], [8], 2, 8⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_20 : (⟨4, 9, [[0, 1, 2]], [3], [8], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_21 : (⟨5, 7, [[0, 1, 2]], [3, 4], [6], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_22 : (⟨5, 9, [[0, 1, 2]], [3, 4], [8], 1, 4⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_23 : (⟨7, 9, [], [6], [8], 2, 8⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_item_24 : (⟨7, 9, [[0, 1, 2]], [6], [8], 1, 5⟩ : TemplateData (Fin 11)).Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t7p24_tableGraph_eq]
  decide

private theorem k11t7p24_templates_fast_block_0_check : ∀ T ∈ k11t7p24_mask_entries_0.map Prod.fst, T.Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t7p24_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t7p24_templates_item_0, k11t7p24_templates_item_1, k11t7p24_templates_item_2, k11t7p24_templates_item_3, k11t7p24_templates_item_4, k11t7p24_templates_item_5, k11t7p24_templates_item_6, k11t7p24_templates_item_7, k11t7p24_templates_item_8, k11t7p24_templates_item_9, k11t7p24_templates_item_10, k11t7p24_templates_item_11, k11t7p24_templates_item_12, k11t7p24_templates_item_13, k11t7p24_templates_item_14, k11t7p24_templates_item_15, k11t7p24_templates_item_16, k11t7p24_templates_item_17, k11t7p24_templates_item_18, k11t7p24_templates_item_19, k11t7p24_templates_item_20, k11t7p24_templates_item_21, k11t7p24_templates_item_22, k11t7p24_templates_item_23, k11t7p24_templates_item_24⟩

private theorem k11t7p24_part_3 : ∀ T ∈ k11t7p24.templates, T.Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t7p24_mask_entries_0.map Prod.fst), T.Check k11t7p24.graph k11t7p24.clique 11 (patternAmount ([[1], [1], [1, 1]] : List (List ℕ))) (([[1], [1], [1, 1]] : List (List ℕ)).map List.length).sum
  exact k11t7p24_templates_fast_block_0_check

private theorem k11t7p24_part_4 : ∀ p ∈ k11t7p24.required, p.Check k11t7p24.graph 11 := by decide

private theorem k11t7p24_part_5 : ClosureCheck k11t7p24.graph (k11t7p24.initialMatrix 11) 11 7 k11t7p24.closure := by
  rw [k11t7p24_initial_eq]
  exact k11t7p24_closure_0

private theorem k11t7p24_part_6 : k11t7p24.bad.Check k11t7p24.graph (k11t7p24.matrix 11) 11 7 := by
  rw [k11t7p24_matrix_eq]
  decide

theorem k11t7p24_check : k11t7p24.Check 11 7 [[1], [1], [1, 1]] :=
  ⟨k11t7p24_part_0, k11t7p24_part_1, k11t7p24_part_2, k11t7p24_part_3, k11t7p24_part_4, k11t7p24_part_5, k11t7p24_part_6⟩
def k11t8p0 : LayoutCertificate 8 where
  chains := [[0], [1], [2], [3], [4], [5], [6], [7]]
  clique := {0, 1, 2, 3, 4, 5, 6, 7}
  templates := [⟨0, 1, [], [], [], 1, 10⟩,
    ⟨0, 2, [], [], [], 1, 10⟩,
    ⟨0, 3, [], [], [], 1, 10⟩,
    ⟨0, 4, [], [], [], 1, 10⟩,
    ⟨1, 2, [], [], [], 1, 10⟩,
    ⟨1, 3, [], [], [], 1, 10⟩,
    ⟨1, 4, [], [], [], 1, 10⟩,
    ⟨1, 5, [], [], [], 1, 10⟩,
    ⟨2, 3, [], [], [], 1, 10⟩,
    ⟨2, 4, [], [], [], 1, 10⟩,
    ⟨2, 5, [], [], [], 1, 10⟩,
    ⟨3, 4, [], [], [], 1, 10⟩,
    ⟨3, 5, [], [], [], 1, 10⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 0), (4, 3), (1, 3), (2, 3), (3, 3)}⟩


private def k11t8p0_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, true, true, true, true, true],
    #[true, false, true, true, true, true, true, true],
    #[true, true, false, true, true, true, true, true],
    #[true, true, true, false, true, true, true, true],
    #[true, true, true, true, false, true, true, true],
    #[true, true, true, true, true, false, true, true],
    #[true, true, true, true, true, true, false, true],
    #[true, true, true, true, true, true, true, false]]

private theorem k11t8p0_adjacency_row_0 : ∀ j : Fin 8,
    k11t8p0.graph.Adj 0 j ↔ adjacencyTableLookup k11t8p0_adjacencyTable 0 j.val = true := by decide

private theorem k11t8p0_adjacency_row_1 : ∀ j : Fin 8,
    k11t8p0.graph.Adj 1 j ↔ adjacencyTableLookup k11t8p0_adjacencyTable 1 j.val = true := by decide

private theorem k11t8p0_adjacency_row_2 : ∀ j : Fin 8,
    k11t8p0.graph.Adj 2 j ↔ adjacencyTableLookup k11t8p0_adjacencyTable 2 j.val = true := by decide

private theorem k11t8p0_adjacency_row_3 : ∀ j : Fin 8,
    k11t8p0.graph.Adj 3 j ↔ adjacencyTableLookup k11t8p0_adjacencyTable 3 j.val = true := by decide

private theorem k11t8p0_adjacency_row_4 : ∀ j : Fin 8,
    k11t8p0.graph.Adj 4 j ↔ adjacencyTableLookup k11t8p0_adjacencyTable 4 j.val = true := by decide

private theorem k11t8p0_adjacency_row_5 : ∀ j : Fin 8,
    k11t8p0.graph.Adj 5 j ↔ adjacencyTableLookup k11t8p0_adjacencyTable 5 j.val = true := by decide

private theorem k11t8p0_adjacency_row_6 : ∀ j : Fin 8,
    k11t8p0.graph.Adj 6 j ↔ adjacencyTableLookup k11t8p0_adjacencyTable 6 j.val = true := by decide

private theorem k11t8p0_adjacency_row_7 : ∀ j : Fin 8,
    k11t8p0.graph.Adj 7 j ↔ adjacencyTableLookup k11t8p0_adjacencyTable 7 j.val = true := by decide

private theorem k11t8p0_adjacency_eq : ∀ i j : Fin 8,
    k11t8p0.graph.Adj i j ↔ adjacencyTableLookup k11t8p0_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t8p0_adjacency_row_0 j

  · exact k11t8p0_adjacency_row_1 j

  · exact k11t8p0_adjacency_row_2 j

  · exact k11t8p0_adjacency_row_3 j

  · exact k11t8p0_adjacency_row_4 j

  · exact k11t8p0_adjacency_row_5 j

  · exact k11t8p0_adjacency_row_6 j

  · exact k11t8p0_adjacency_row_7 j

private def k11t8p0_tableGraph : SimpleGraph (Fin 8) :=
  adjacencyTableGraph k11t8p0.graph k11t8p0_adjacencyTable k11t8p0_adjacency_eq

private instance k11t8p0_tableGraph_decidableAdj :
    DecidableRel k11t8p0_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t8p0_adjacencyTable i.val j.val = true))

private theorem k11t8p0_tableGraph_eq : k11t8p0_tableGraph = k11t8p0.graph :=
  adjacencyTableGraph_eq k11t8p0.graph k11t8p0_adjacencyTable k11t8p0_adjacency_eq

private def k11t8p0_state_0 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, ∅, ∅, ∅],
    #[Finset.Icc 1 10, ∅, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, ∅, ∅],
    #[Finset.Icc 1 10, Finset.Icc 1 10, ∅, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, ∅, ∅],
    #[Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, ∅, Finset.Icc 1 10, Finset.Icc 1 10, ∅, ∅],
    #[Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, ∅, ∅, ∅, ∅],
    #[∅, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t8p0_decode_entry_0 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_1 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_2 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_3 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_4 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_5 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_6 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_7 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_8 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_9 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_10 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_11 : decode 12 2046 = Finset.Icc 1 10 := by decide

private theorem k11t8p0_decode_entry_12 : decode 12 2046 = Finset.Icc 1 10 := by decide

private def k11t8p0_mask_entries_0 : List (TemplateData (Fin 8) × ℕ) := [(⟨0, 1, [], [], [], 1, 10⟩, 2046), (⟨0, 2, [], [], [], 1, 10⟩, 2046), (⟨0, 3, [], [], [], 1, 10⟩, 2046), (⟨0, 4, [], [], [], 1, 10⟩, 2046), (⟨1, 2, [], [], [], 1, 10⟩, 2046), (⟨1, 3, [], [], [], 1, 10⟩, 2046), (⟨1, 4, [], [], [], 1, 10⟩, 2046), (⟨1, 5, [], [], [], 1, 10⟩, 2046), (⟨2, 3, [], [], [], 1, 10⟩, 2046), (⟨2, 4, [], [], [], 1, 10⟩, 2046), (⟨2, 5, [], [], [], 1, 10⟩, 2046), (⟨3, 4, [], [], [], 1, 10⟩, 2046), (⟨3, 5, [], [], [], 1, 10⟩, 2046)]

private theorem k11t8p0_decode_entries_0 : ∀ Tb ∈ k11t8p0_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t8p0_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p0_decode_entry_0, k11t8p0_decode_entry_1, k11t8p0_decode_entry_2, k11t8p0_decode_entry_3, k11t8p0_decode_entry_4, k11t8p0_decode_entry_5, k11t8p0_decode_entry_6, k11t8p0_decode_entry_7, k11t8p0_decode_entry_8, k11t8p0_decode_entry_9, k11t8p0_decode_entry_10, k11t8p0_decode_entry_11, k11t8p0_decode_entry_12⟩

private def k11t8p0_mask_block_0 : Fin 8 → Fin 8 → ℕ :=
  fun i j => ((#[#[0, 2046, 2046, 2046, 2046, 0, 0, 0],
    #[2046, 0, 2046, 2046, 2046, 2046, 0, 0],
    #[2046, 2046, 0, 2046, 2046, 2046, 0, 0],
    #[2046, 2046, 2046, 0, 2046, 2046, 0, 0],
    #[2046, 2046, 2046, 2046, 0, 0, 0, 0],
    #[0, 2046, 2046, 2046, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p0_mask_block_0_eq_row_0 : ∀ j : Fin 8, (templateMaskMatrix k11t8p0_mask_entries_0) 0 j = k11t8p0_mask_block_0 0 j := by decide

private theorem k11t8p0_mask_block_0_eq_row_1 : ∀ j : Fin 8, (templateMaskMatrix k11t8p0_mask_entries_0) 1 j = k11t8p0_mask_block_0 1 j := by decide

private theorem k11t8p0_mask_block_0_eq_row_2 : ∀ j : Fin 8, (templateMaskMatrix k11t8p0_mask_entries_0) 2 j = k11t8p0_mask_block_0 2 j := by decide

private theorem k11t8p0_mask_block_0_eq_row_3 : ∀ j : Fin 8, (templateMaskMatrix k11t8p0_mask_entries_0) 3 j = k11t8p0_mask_block_0 3 j := by decide

private theorem k11t8p0_mask_block_0_eq_row_4 : ∀ j : Fin 8, (templateMaskMatrix k11t8p0_mask_entries_0) 4 j = k11t8p0_mask_block_0 4 j := by decide

private theorem k11t8p0_mask_block_0_eq_row_5 : ∀ j : Fin 8, (templateMaskMatrix k11t8p0_mask_entries_0) 5 j = k11t8p0_mask_block_0 5 j := by decide

private theorem k11t8p0_mask_block_0_eq_row_6 : ∀ j : Fin 8, (templateMaskMatrix k11t8p0_mask_entries_0) 6 j = k11t8p0_mask_block_0 6 j := by decide

private theorem k11t8p0_mask_block_0_eq_row_7 : ∀ j : Fin 8, (templateMaskMatrix k11t8p0_mask_entries_0) 7 j = k11t8p0_mask_block_0 7 j := by decide

private theorem k11t8p0_mask_block_0_eq : (templateMaskMatrix k11t8p0_mask_entries_0) = k11t8p0_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t8p0_mask_block_0_eq_row_0 j

  · exact k11t8p0_mask_block_0_eq_row_1 j

  · exact k11t8p0_mask_block_0_eq_row_2 j

  · exact k11t8p0_mask_block_0_eq_row_3 j

  · exact k11t8p0_mask_block_0_eq_row_4 j

  · exact k11t8p0_mask_block_0_eq_row_5 j

  · exact k11t8p0_mask_block_0_eq_row_6 j

  · exact k11t8p0_mask_block_0_eq_row_7 j

private def k11t8p0_mask_entries : List (TemplateData (Fin 8) × ℕ) := k11t8p0_mask_entries_0

private theorem k11t8p0_decode_entries : ∀ Tb ∈ k11t8p0_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t8p0_decode_entries_0

private theorem k11t8p0_mask_entries_map : k11t8p0_mask_entries.map Prod.fst = k11t8p0.templates := by rfl

private def k11t8p0_template_mask : Fin 8 → Fin 8 → ℕ :=
  fun i j => ((#[#[0, 2046, 2046, 2046, 2046, 0, 0, 0],
    #[2046, 0, 2046, 2046, 2046, 2046, 0, 0],
    #[2046, 2046, 0, 2046, 2046, 2046, 0, 0],
    #[2046, 2046, 2046, 0, 2046, 2046, 0, 0],
    #[2046, 2046, 2046, 2046, 0, 0, 0, 0],
    #[0, 2046, 2046, 2046, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p0_mask_merged_eq_row_0 : ∀ j : Fin 8, (fun i j => k11t8p0_mask_block_0 i j) 0 j = k11t8p0_template_mask 0 j := by decide

private theorem k11t8p0_mask_merged_eq_row_1 : ∀ j : Fin 8, (fun i j => k11t8p0_mask_block_0 i j) 1 j = k11t8p0_template_mask 1 j := by decide

private theorem k11t8p0_mask_merged_eq_row_2 : ∀ j : Fin 8, (fun i j => k11t8p0_mask_block_0 i j) 2 j = k11t8p0_template_mask 2 j := by decide

private theorem k11t8p0_mask_merged_eq_row_3 : ∀ j : Fin 8, (fun i j => k11t8p0_mask_block_0 i j) 3 j = k11t8p0_template_mask 3 j := by decide

private theorem k11t8p0_mask_merged_eq_row_4 : ∀ j : Fin 8, (fun i j => k11t8p0_mask_block_0 i j) 4 j = k11t8p0_template_mask 4 j := by decide

private theorem k11t8p0_mask_merged_eq_row_5 : ∀ j : Fin 8, (fun i j => k11t8p0_mask_block_0 i j) 5 j = k11t8p0_template_mask 5 j := by decide

private theorem k11t8p0_mask_merged_eq_row_6 : ∀ j : Fin 8, (fun i j => k11t8p0_mask_block_0 i j) 6 j = k11t8p0_template_mask 6 j := by decide

private theorem k11t8p0_mask_merged_eq_row_7 : ∀ j : Fin 8, (fun i j => k11t8p0_mask_block_0 i j) 7 j = k11t8p0_template_mask 7 j := by decide

private theorem k11t8p0_mask_merged_eq : (fun i j => k11t8p0_mask_block_0 i j) = k11t8p0_template_mask := by
  funext i j
  fin_cases i

  · exact k11t8p0_mask_merged_eq_row_0 j

  · exact k11t8p0_mask_merged_eq_row_1 j

  · exact k11t8p0_mask_merged_eq_row_2 j

  · exact k11t8p0_mask_merged_eq_row_3 j

  · exact k11t8p0_mask_merged_eq_row_4 j

  · exact k11t8p0_mask_merged_eq_row_5 j

  · exact k11t8p0_mask_merged_eq_row_6 j

  · exact k11t8p0_mask_merged_eq_row_7 j

private theorem k11t8p0_template_mask_eq : templateMaskMatrix k11t8p0_mask_entries = k11t8p0_template_mask := by
  funext i j
  change templateMaskMatrix (k11t8p0_mask_entries_0) i j = _
  simp only [k11t8p0_mask_block_0_eq]
  exact congrFun (congrFun k11t8p0_mask_merged_eq i) j

private theorem k11t8p0_initial_decoded_eq_row_0 : ∀ j : Fin 8, (fun i j => decode 12 (k11t8p0_template_mask i j) ∪ requiredMatrix 11 k11t8p0.required i j) 0 j = k11t8p0_state_0 0 j := by decide

private theorem k11t8p0_initial_decoded_eq_row_1 : ∀ j : Fin 8, (fun i j => decode 12 (k11t8p0_template_mask i j) ∪ requiredMatrix 11 k11t8p0.required i j) 1 j = k11t8p0_state_0 1 j := by decide

private theorem k11t8p0_initial_decoded_eq_row_2 : ∀ j : Fin 8, (fun i j => decode 12 (k11t8p0_template_mask i j) ∪ requiredMatrix 11 k11t8p0.required i j) 2 j = k11t8p0_state_0 2 j := by decide

private theorem k11t8p0_initial_decoded_eq_row_3 : ∀ j : Fin 8, (fun i j => decode 12 (k11t8p0_template_mask i j) ∪ requiredMatrix 11 k11t8p0.required i j) 3 j = k11t8p0_state_0 3 j := by decide

private theorem k11t8p0_initial_decoded_eq_row_4 : ∀ j : Fin 8, (fun i j => decode 12 (k11t8p0_template_mask i j) ∪ requiredMatrix 11 k11t8p0.required i j) 4 j = k11t8p0_state_0 4 j := by decide

private theorem k11t8p0_initial_decoded_eq_row_5 : ∀ j : Fin 8, (fun i j => decode 12 (k11t8p0_template_mask i j) ∪ requiredMatrix 11 k11t8p0.required i j) 5 j = k11t8p0_state_0 5 j := by decide

private theorem k11t8p0_initial_decoded_eq_row_6 : ∀ j : Fin 8, (fun i j => decode 12 (k11t8p0_template_mask i j) ∪ requiredMatrix 11 k11t8p0.required i j) 6 j = k11t8p0_state_0 6 j := by decide

private theorem k11t8p0_initial_decoded_eq_row_7 : ∀ j : Fin 8, (fun i j => decode 12 (k11t8p0_template_mask i j) ∪ requiredMatrix 11 k11t8p0.required i j) 7 j = k11t8p0_state_0 7 j := by decide

private theorem k11t8p0_initial_decoded_eq : (fun i j => decode 12 (k11t8p0_template_mask i j) ∪ requiredMatrix 11 k11t8p0.required i j) = k11t8p0_state_0 := by
  funext i j
  fin_cases i

  · exact k11t8p0_initial_decoded_eq_row_0 j

  · exact k11t8p0_initial_decoded_eq_row_1 j

  · exact k11t8p0_initial_decoded_eq_row_2 j

  · exact k11t8p0_initial_decoded_eq_row_3 j

  · exact k11t8p0_initial_decoded_eq_row_4 j

  · exact k11t8p0_initial_decoded_eq_row_5 j

  · exact k11t8p0_initial_decoded_eq_row_6 j

  · exact k11t8p0_initial_decoded_eq_row_7 j

private theorem k11t8p0_initial_eq : k11t8p0.initialMatrix 11 = k11t8p0_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t8p0_mask_entries k11t8p0_decode_entries
  rw [k11t8p0_mask_entries_map, k11t8p0_template_mask_eq] at h
  funext i j
  change templateMatrix k11t8p0.templates i j ∪ requiredMatrix 11 k11t8p0.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t8p0_initial_decoded_eq i) j

private theorem k11t8p0_closure_0 : ClosureCheck k11t8p0.graph k11t8p0_state_0 11 8 [] := by trivial

private theorem k11t8p0_matrix_eq : k11t8p0.matrix 11 = k11t8p0_state_0 := by
  change closureMatrix (k11t8p0.initialMatrix 11) _ = _
  rw [k11t8p0_initial_eq]
  change closureMatrix k11t8p0_state_0 [] = _
  rfl

private theorem k11t8p0_part_0 : k11t8p0.chains.flatten = List.finRange _ := by decide

private theorem k11t8p0_part_1 : k11t8p0.chains.map List.length = ([[], [], [], [], [], [], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t8p0_part_2 : k11t8p0.chains.map (fun l => l.map (fun i => decide (i ∈ k11t8p0.clique))) = ([[], [], [], [], [], [], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k11t8p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_2 : (⟨0, 3, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_3 : (⟨0, 4, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_4 : (⟨1, 2, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_5 : (⟨1, 3, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_6 : (⟨1, 4, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_7 : (⟨1, 5, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_8 : (⟨2, 3, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_9 : (⟨2, 4, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_10 : (⟨2, 5, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_11 : (⟨3, 4, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_item_12 : (⟨3, 5, [], [], [], 1, 10⟩ : TemplateData (Fin 8)).Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p0_tableGraph_eq]
  decide

private theorem k11t8p0_templates_fast_block_0_check : ∀ T ∈ k11t8p0_mask_entries_0.map Prod.fst, T.Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k11t8p0_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p0_templates_item_0, k11t8p0_templates_item_1, k11t8p0_templates_item_2, k11t8p0_templates_item_3, k11t8p0_templates_item_4, k11t8p0_templates_item_5, k11t8p0_templates_item_6, k11t8p0_templates_item_7, k11t8p0_templates_item_8, k11t8p0_templates_item_9, k11t8p0_templates_item_10, k11t8p0_templates_item_11, k11t8p0_templates_item_12⟩

private theorem k11t8p0_part_3 : ∀ T ∈ k11t8p0.templates, T.Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t8p0_mask_entries_0.map Prod.fst), T.Check k11t8p0.graph k11t8p0.clique 11 (patternAmount ([[], [], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum
  exact k11t8p0_templates_fast_block_0_check

private theorem k11t8p0_part_4 : ∀ p ∈ k11t8p0.required, p.Check k11t8p0.graph 11 := by decide

private theorem k11t8p0_part_5 : ClosureCheck k11t8p0.graph (k11t8p0.initialMatrix 11) 11 8 k11t8p0.closure := by
  rw [k11t8p0_initial_eq]
  exact k11t8p0_closure_0

private theorem k11t8p0_part_6 : k11t8p0.bad.Check k11t8p0.graph (k11t8p0.matrix 11) 11 8 := by
  rw [k11t8p0_matrix_eq]
  decide

theorem k11t8p0_check : k11t8p0.Check 11 8 [[], [], [], [], [], [], [], []] :=
  ⟨k11t8p0_part_0, k11t8p0_part_1, k11t8p0_part_2, k11t8p0_part_3, k11t8p0_part_4, k11t8p0_part_5, k11t8p0_part_6⟩
def k11t8p1 : LayoutCertificate 9 where
  chains := [[0], [1], [2], [3], [4], [5], [6, 7, 8]]
  clique := {0, 1, 2, 3, 4, 5, 6, 8}
  templates := [⟨0, 1, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨0, 2, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨0, 3, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨0, 4, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨0, 5, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨0, 7, [], [], [6], 1, 9⟩,
    ⟨1, 2, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨1, 3, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨1, 4, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨1, 5, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨1, 7, [], [], [6], 1, 9⟩,
    ⟨2, 3, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨2, 4, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨2, 5, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨2, 7, [], [], [6], 1, 9⟩,
    ⟨3, 4, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨3, 5, [[6, 7, 8]], [], [], 1, 7⟩,
    ⟨3, 7, [], [], [6], 1, 9⟩]
  required := []
  closure := []
  bad := ⟨none, {(7, 0), (0, 2), (1, 3), (2, 3), (3, 3)}⟩


private def k11t8p1_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, true, true, true, true, false, true],
    #[true, false, true, true, true, true, true, false, true],
    #[true, true, false, true, true, true, true, false, true],
    #[true, true, true, false, true, true, true, false, true],
    #[true, true, true, true, false, true, true, false, true],
    #[true, true, true, true, true, false, true, false, true],
    #[true, true, true, true, true, true, false, true, true],
    #[false, false, false, false, false, false, true, false, true],
    #[true, true, true, true, true, true, true, true, false]]

private theorem k11t8p1_adjacency_row_0 : ∀ j : Fin 9,
    k11t8p1.graph.Adj 0 j ↔ adjacencyTableLookup k11t8p1_adjacencyTable 0 j.val = true := by decide

private theorem k11t8p1_adjacency_row_1 : ∀ j : Fin 9,
    k11t8p1.graph.Adj 1 j ↔ adjacencyTableLookup k11t8p1_adjacencyTable 1 j.val = true := by decide

private theorem k11t8p1_adjacency_row_2 : ∀ j : Fin 9,
    k11t8p1.graph.Adj 2 j ↔ adjacencyTableLookup k11t8p1_adjacencyTable 2 j.val = true := by decide

private theorem k11t8p1_adjacency_row_3 : ∀ j : Fin 9,
    k11t8p1.graph.Adj 3 j ↔ adjacencyTableLookup k11t8p1_adjacencyTable 3 j.val = true := by decide

private theorem k11t8p1_adjacency_row_4 : ∀ j : Fin 9,
    k11t8p1.graph.Adj 4 j ↔ adjacencyTableLookup k11t8p1_adjacencyTable 4 j.val = true := by decide

private theorem k11t8p1_adjacency_row_5 : ∀ j : Fin 9,
    k11t8p1.graph.Adj 5 j ↔ adjacencyTableLookup k11t8p1_adjacencyTable 5 j.val = true := by decide

private theorem k11t8p1_adjacency_row_6 : ∀ j : Fin 9,
    k11t8p1.graph.Adj 6 j ↔ adjacencyTableLookup k11t8p1_adjacencyTable 6 j.val = true := by decide

private theorem k11t8p1_adjacency_row_7 : ∀ j : Fin 9,
    k11t8p1.graph.Adj 7 j ↔ adjacencyTableLookup k11t8p1_adjacencyTable 7 j.val = true := by decide

private theorem k11t8p1_adjacency_row_8 : ∀ j : Fin 9,
    k11t8p1.graph.Adj 8 j ↔ adjacencyTableLookup k11t8p1_adjacencyTable 8 j.val = true := by decide

private theorem k11t8p1_adjacency_eq : ∀ i j : Fin 9,
    k11t8p1.graph.Adj i j ↔ adjacencyTableLookup k11t8p1_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t8p1_adjacency_row_0 j

  · exact k11t8p1_adjacency_row_1 j

  · exact k11t8p1_adjacency_row_2 j

  · exact k11t8p1_adjacency_row_3 j

  · exact k11t8p1_adjacency_row_4 j

  · exact k11t8p1_adjacency_row_5 j

  · exact k11t8p1_adjacency_row_6 j

  · exact k11t8p1_adjacency_row_7 j

  · exact k11t8p1_adjacency_row_8 j

private def k11t8p1_tableGraph : SimpleGraph (Fin 9) :=
  adjacencyTableGraph k11t8p1.graph k11t8p1_adjacencyTable k11t8p1_adjacency_eq

private instance k11t8p1_tableGraph_decidableAdj :
    DecidableRel k11t8p1_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t8p1_adjacencyTable i.val j.val = true))

private theorem k11t8p1_tableGraph_eq : k11t8p1_tableGraph = k11t8p1.graph :=
  adjacencyTableGraph_eq k11t8p1.graph k11t8p1_adjacencyTable k11t8p1_adjacency_eq

private def k11t8p1_state_0 : ForbiddenMatrix 9 :=
  fun i j => ((#[#[∅, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, ∅, Finset.Icc 1 9, ∅],
    #[Finset.Icc 1 7, ∅, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, ∅, Finset.Icc 1 9, ∅],
    #[Finset.Icc 1 7, Finset.Icc 1 7, ∅, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, ∅, Finset.Icc 1 9, ∅],
    #[Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, ∅, Finset.Icc 1 7, Finset.Icc 1 7, ∅, Finset.Icc 1 9, ∅],
    #[Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t8p1_decode_entry_0 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_1 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_2 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_3 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_4 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_5 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p1_decode_entry_6 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_7 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_8 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_9 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_10 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p1_decode_entry_11 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_12 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_13 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_14 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p1_decode_entry_15 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_16 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p1_decode_entry_17 : decode 12 1022 = Finset.Icc 1 9 := by decide

private def k11t8p1_mask_entries_0 : List (TemplateData (Fin 9) × ℕ) := [(⟨0, 1, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨0, 2, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨0, 3, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨0, 4, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨0, 5, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨0, 7, [], [], [6], 1, 9⟩, 1022), (⟨1, 2, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨1, 3, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨1, 4, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨1, 5, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨1, 7, [], [], [6], 1, 9⟩, 1022), (⟨2, 3, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨2, 4, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨2, 5, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨2, 7, [], [], [6], 1, 9⟩, 1022), (⟨3, 4, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨3, 5, [[6, 7, 8]], [], [], 1, 7⟩, 254), (⟨3, 7, [], [], [6], 1, 9⟩, 1022)]

private theorem k11t8p1_decode_entries_0 : ∀ Tb ∈ k11t8p1_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t8p1_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p1_decode_entry_0, k11t8p1_decode_entry_1, k11t8p1_decode_entry_2, k11t8p1_decode_entry_3, k11t8p1_decode_entry_4, k11t8p1_decode_entry_5, k11t8p1_decode_entry_6, k11t8p1_decode_entry_7, k11t8p1_decode_entry_8, k11t8p1_decode_entry_9, k11t8p1_decode_entry_10, k11t8p1_decode_entry_11, k11t8p1_decode_entry_12, k11t8p1_decode_entry_13, k11t8p1_decode_entry_14, k11t8p1_decode_entry_15, k11t8p1_decode_entry_16, k11t8p1_decode_entry_17⟩

private def k11t8p1_mask_block_0 : Fin 9 → Fin 9 → ℕ :=
  fun i j => ((#[#[0, 254, 254, 254, 254, 254, 0, 1022, 0],
    #[254, 0, 254, 254, 254, 254, 0, 1022, 0],
    #[254, 254, 0, 254, 254, 254, 0, 1022, 0],
    #[254, 254, 254, 0, 254, 254, 0, 1022, 0],
    #[254, 254, 254, 254, 0, 0, 0, 0, 0],
    #[254, 254, 254, 254, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1022, 1022, 1022, 1022, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p1_mask_block_0_eq_row_0 : ∀ j : Fin 9, (templateMaskMatrix k11t8p1_mask_entries_0) 0 j = k11t8p1_mask_block_0 0 j := by decide

private theorem k11t8p1_mask_block_0_eq_row_1 : ∀ j : Fin 9, (templateMaskMatrix k11t8p1_mask_entries_0) 1 j = k11t8p1_mask_block_0 1 j := by decide

private theorem k11t8p1_mask_block_0_eq_row_2 : ∀ j : Fin 9, (templateMaskMatrix k11t8p1_mask_entries_0) 2 j = k11t8p1_mask_block_0 2 j := by decide

private theorem k11t8p1_mask_block_0_eq_row_3 : ∀ j : Fin 9, (templateMaskMatrix k11t8p1_mask_entries_0) 3 j = k11t8p1_mask_block_0 3 j := by decide

private theorem k11t8p1_mask_block_0_eq_row_4 : ∀ j : Fin 9, (templateMaskMatrix k11t8p1_mask_entries_0) 4 j = k11t8p1_mask_block_0 4 j := by decide

private theorem k11t8p1_mask_block_0_eq_row_5 : ∀ j : Fin 9, (templateMaskMatrix k11t8p1_mask_entries_0) 5 j = k11t8p1_mask_block_0 5 j := by decide

private theorem k11t8p1_mask_block_0_eq_row_6 : ∀ j : Fin 9, (templateMaskMatrix k11t8p1_mask_entries_0) 6 j = k11t8p1_mask_block_0 6 j := by decide

private theorem k11t8p1_mask_block_0_eq_row_7 : ∀ j : Fin 9, (templateMaskMatrix k11t8p1_mask_entries_0) 7 j = k11t8p1_mask_block_0 7 j := by decide

private theorem k11t8p1_mask_block_0_eq_row_8 : ∀ j : Fin 9, (templateMaskMatrix k11t8p1_mask_entries_0) 8 j = k11t8p1_mask_block_0 8 j := by decide

private theorem k11t8p1_mask_block_0_eq : (templateMaskMatrix k11t8p1_mask_entries_0) = k11t8p1_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t8p1_mask_block_0_eq_row_0 j

  · exact k11t8p1_mask_block_0_eq_row_1 j

  · exact k11t8p1_mask_block_0_eq_row_2 j

  · exact k11t8p1_mask_block_0_eq_row_3 j

  · exact k11t8p1_mask_block_0_eq_row_4 j

  · exact k11t8p1_mask_block_0_eq_row_5 j

  · exact k11t8p1_mask_block_0_eq_row_6 j

  · exact k11t8p1_mask_block_0_eq_row_7 j

  · exact k11t8p1_mask_block_0_eq_row_8 j

private def k11t8p1_mask_entries : List (TemplateData (Fin 9) × ℕ) := k11t8p1_mask_entries_0

private theorem k11t8p1_decode_entries : ∀ Tb ∈ k11t8p1_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t8p1_decode_entries_0

private theorem k11t8p1_mask_entries_map : k11t8p1_mask_entries.map Prod.fst = k11t8p1.templates := by rfl

private def k11t8p1_template_mask : Fin 9 → Fin 9 → ℕ :=
  fun i j => ((#[#[0, 254, 254, 254, 254, 254, 0, 1022, 0],
    #[254, 0, 254, 254, 254, 254, 0, 1022, 0],
    #[254, 254, 0, 254, 254, 254, 0, 1022, 0],
    #[254, 254, 254, 0, 254, 254, 0, 1022, 0],
    #[254, 254, 254, 254, 0, 0, 0, 0, 0],
    #[254, 254, 254, 254, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1022, 1022, 1022, 1022, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p1_mask_merged_eq_row_0 : ∀ j : Fin 9, (fun i j => k11t8p1_mask_block_0 i j) 0 j = k11t8p1_template_mask 0 j := by decide

private theorem k11t8p1_mask_merged_eq_row_1 : ∀ j : Fin 9, (fun i j => k11t8p1_mask_block_0 i j) 1 j = k11t8p1_template_mask 1 j := by decide

private theorem k11t8p1_mask_merged_eq_row_2 : ∀ j : Fin 9, (fun i j => k11t8p1_mask_block_0 i j) 2 j = k11t8p1_template_mask 2 j := by decide

private theorem k11t8p1_mask_merged_eq_row_3 : ∀ j : Fin 9, (fun i j => k11t8p1_mask_block_0 i j) 3 j = k11t8p1_template_mask 3 j := by decide

private theorem k11t8p1_mask_merged_eq_row_4 : ∀ j : Fin 9, (fun i j => k11t8p1_mask_block_0 i j) 4 j = k11t8p1_template_mask 4 j := by decide

private theorem k11t8p1_mask_merged_eq_row_5 : ∀ j : Fin 9, (fun i j => k11t8p1_mask_block_0 i j) 5 j = k11t8p1_template_mask 5 j := by decide

private theorem k11t8p1_mask_merged_eq_row_6 : ∀ j : Fin 9, (fun i j => k11t8p1_mask_block_0 i j) 6 j = k11t8p1_template_mask 6 j := by decide

private theorem k11t8p1_mask_merged_eq_row_7 : ∀ j : Fin 9, (fun i j => k11t8p1_mask_block_0 i j) 7 j = k11t8p1_template_mask 7 j := by decide

private theorem k11t8p1_mask_merged_eq_row_8 : ∀ j : Fin 9, (fun i j => k11t8p1_mask_block_0 i j) 8 j = k11t8p1_template_mask 8 j := by decide

private theorem k11t8p1_mask_merged_eq : (fun i j => k11t8p1_mask_block_0 i j) = k11t8p1_template_mask := by
  funext i j
  fin_cases i

  · exact k11t8p1_mask_merged_eq_row_0 j

  · exact k11t8p1_mask_merged_eq_row_1 j

  · exact k11t8p1_mask_merged_eq_row_2 j

  · exact k11t8p1_mask_merged_eq_row_3 j

  · exact k11t8p1_mask_merged_eq_row_4 j

  · exact k11t8p1_mask_merged_eq_row_5 j

  · exact k11t8p1_mask_merged_eq_row_6 j

  · exact k11t8p1_mask_merged_eq_row_7 j

  · exact k11t8p1_mask_merged_eq_row_8 j

private theorem k11t8p1_template_mask_eq : templateMaskMatrix k11t8p1_mask_entries = k11t8p1_template_mask := by
  funext i j
  change templateMaskMatrix (k11t8p1_mask_entries_0) i j = _
  simp only [k11t8p1_mask_block_0_eq]
  exact congrFun (congrFun k11t8p1_mask_merged_eq i) j

private theorem k11t8p1_initial_decoded_eq_row_0 : ∀ j : Fin 9, (fun i j => decode 12 (k11t8p1_template_mask i j) ∪ requiredMatrix 11 k11t8p1.required i j) 0 j = k11t8p1_state_0 0 j := by decide

private theorem k11t8p1_initial_decoded_eq_row_1 : ∀ j : Fin 9, (fun i j => decode 12 (k11t8p1_template_mask i j) ∪ requiredMatrix 11 k11t8p1.required i j) 1 j = k11t8p1_state_0 1 j := by decide

private theorem k11t8p1_initial_decoded_eq_row_2 : ∀ j : Fin 9, (fun i j => decode 12 (k11t8p1_template_mask i j) ∪ requiredMatrix 11 k11t8p1.required i j) 2 j = k11t8p1_state_0 2 j := by decide

private theorem k11t8p1_initial_decoded_eq_row_3 : ∀ j : Fin 9, (fun i j => decode 12 (k11t8p1_template_mask i j) ∪ requiredMatrix 11 k11t8p1.required i j) 3 j = k11t8p1_state_0 3 j := by decide

private theorem k11t8p1_initial_decoded_eq_row_4 : ∀ j : Fin 9, (fun i j => decode 12 (k11t8p1_template_mask i j) ∪ requiredMatrix 11 k11t8p1.required i j) 4 j = k11t8p1_state_0 4 j := by decide

private theorem k11t8p1_initial_decoded_eq_row_5 : ∀ j : Fin 9, (fun i j => decode 12 (k11t8p1_template_mask i j) ∪ requiredMatrix 11 k11t8p1.required i j) 5 j = k11t8p1_state_0 5 j := by decide

private theorem k11t8p1_initial_decoded_eq_row_6 : ∀ j : Fin 9, (fun i j => decode 12 (k11t8p1_template_mask i j) ∪ requiredMatrix 11 k11t8p1.required i j) 6 j = k11t8p1_state_0 6 j := by decide

private theorem k11t8p1_initial_decoded_eq_row_7 : ∀ j : Fin 9, (fun i j => decode 12 (k11t8p1_template_mask i j) ∪ requiredMatrix 11 k11t8p1.required i j) 7 j = k11t8p1_state_0 7 j := by decide

private theorem k11t8p1_initial_decoded_eq_row_8 : ∀ j : Fin 9, (fun i j => decode 12 (k11t8p1_template_mask i j) ∪ requiredMatrix 11 k11t8p1.required i j) 8 j = k11t8p1_state_0 8 j := by decide

private theorem k11t8p1_initial_decoded_eq : (fun i j => decode 12 (k11t8p1_template_mask i j) ∪ requiredMatrix 11 k11t8p1.required i j) = k11t8p1_state_0 := by
  funext i j
  fin_cases i

  · exact k11t8p1_initial_decoded_eq_row_0 j

  · exact k11t8p1_initial_decoded_eq_row_1 j

  · exact k11t8p1_initial_decoded_eq_row_2 j

  · exact k11t8p1_initial_decoded_eq_row_3 j

  · exact k11t8p1_initial_decoded_eq_row_4 j

  · exact k11t8p1_initial_decoded_eq_row_5 j

  · exact k11t8p1_initial_decoded_eq_row_6 j

  · exact k11t8p1_initial_decoded_eq_row_7 j

  · exact k11t8p1_initial_decoded_eq_row_8 j

private theorem k11t8p1_initial_eq : k11t8p1.initialMatrix 11 = k11t8p1_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t8p1_mask_entries k11t8p1_decode_entries
  rw [k11t8p1_mask_entries_map, k11t8p1_template_mask_eq] at h
  funext i j
  change templateMatrix k11t8p1.templates i j ∪ requiredMatrix 11 k11t8p1.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t8p1_initial_decoded_eq i) j

private theorem k11t8p1_closure_0 : ClosureCheck k11t8p1.graph k11t8p1_state_0 11 8 [] := by trivial

private theorem k11t8p1_matrix_eq : k11t8p1.matrix 11 = k11t8p1_state_0 := by
  change closureMatrix (k11t8p1.initialMatrix 11) _ = _
  rw [k11t8p1_initial_eq]
  change closureMatrix k11t8p1_state_0 [] = _
  rfl

private theorem k11t8p1_part_0 : k11t8p1.chains.flatten = List.finRange _ := by decide

private theorem k11t8p1_part_1 : k11t8p1.chains.map List.length = ([[], [], [], [], [], [], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t8p1_part_2 : k11t8p1.chains.map (fun l => l.map (fun i => decide (i ∈ k11t8p1.clique))) = ([[], [], [], [], [], [], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k11t8p1_templates_item_0 : (⟨0, 1, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_1 : (⟨0, 2, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_2 : (⟨0, 3, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_3 : (⟨0, 4, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_4 : (⟨0, 5, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_5 : (⟨0, 7, [], [], [6], 1, 9⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_6 : (⟨1, 2, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_7 : (⟨1, 3, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_8 : (⟨1, 4, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_9 : (⟨1, 5, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_10 : (⟨1, 7, [], [], [6], 1, 9⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_11 : (⟨2, 3, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_12 : (⟨2, 4, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_13 : (⟨2, 5, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_14 : (⟨2, 7, [], [], [6], 1, 9⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_15 : (⟨3, 4, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_16 : (⟨3, 5, [[6, 7, 8]], [], [], 1, 7⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_item_17 : (⟨3, 7, [], [], [6], 1, 9⟩ : TemplateData (Fin 9)).Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p1_tableGraph_eq]
  decide

private theorem k11t8p1_templates_fast_block_0_check : ∀ T ∈ k11t8p1_mask_entries_0.map Prod.fst, T.Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t8p1_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p1_templates_item_0, k11t8p1_templates_item_1, k11t8p1_templates_item_2, k11t8p1_templates_item_3, k11t8p1_templates_item_4, k11t8p1_templates_item_5, k11t8p1_templates_item_6, k11t8p1_templates_item_7, k11t8p1_templates_item_8, k11t8p1_templates_item_9, k11t8p1_templates_item_10, k11t8p1_templates_item_11, k11t8p1_templates_item_12, k11t8p1_templates_item_13, k11t8p1_templates_item_14, k11t8p1_templates_item_15, k11t8p1_templates_item_16, k11t8p1_templates_item_17⟩

private theorem k11t8p1_part_3 : ∀ T ∈ k11t8p1.templates, T.Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t8p1_mask_entries_0.map Prod.fst), T.Check k11t8p1.graph k11t8p1.clique 11 (patternAmount ([[], [], [], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [], [], [1]] : List (List ℕ)).map List.length).sum
  exact k11t8p1_templates_fast_block_0_check

private theorem k11t8p1_part_4 : ∀ p ∈ k11t8p1.required, p.Check k11t8p1.graph 11 := by decide

private theorem k11t8p1_part_5 : ClosureCheck k11t8p1.graph (k11t8p1.initialMatrix 11) 11 8 k11t8p1.closure := by
  rw [k11t8p1_initial_eq]
  exact k11t8p1_closure_0

private theorem k11t8p1_part_6 : k11t8p1.bad.Check k11t8p1.graph (k11t8p1.matrix 11) 11 8 := by
  rw [k11t8p1_matrix_eq]
  decide

theorem k11t8p1_check : k11t8p1.Check 11 8 [[], [], [], [], [], [], [1]] :=
  ⟨k11t8p1_part_0, k11t8p1_part_1, k11t8p1_part_2, k11t8p1_part_3, k11t8p1_part_4, k11t8p1_part_5, k11t8p1_part_6⟩
def k11t8p2 : LayoutCertificate 10 where
  chains := [[0], [1], [2], [3], [4], [5], [6, 7, 8, 9]]
  clique := {0, 1, 2, 3, 4, 5, 6, 9}
  templates := [⟨0, 1, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨0, 2, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨0, 3, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨0, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨0, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨0, 6, [], [], [7, 8, 9], 1, 7⟩,
    ⟨0, 7, [], [], [8, 9], 1, 8⟩,
    ⟨1, 2, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨1, 3, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨1, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨1, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨1, 6, [], [], [7, 8, 9], 1, 7⟩,
    ⟨1, 7, [], [], [8, 9], 1, 8⟩,
    ⟨2, 3, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨2, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨2, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨2, 6, [], [], [7, 8, 9], 1, 7⟩,
    ⟨2, 7, [], [], [8, 9], 1, 8⟩,
    ⟨3, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨3, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩,
    ⟨3, 6, [], [], [7, 8, 9], 1, 7⟩,
    ⟨3, 7, [], [], [8, 9], 1, 8⟩]
  required := []
  closure := []
  bad := ⟨none, {(4, 0), (0, 2), (1, 3), (2, 3), (3, 3)}⟩


private def k11t8p2_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, true, true, true, true, false, false, true],
    #[true, false, true, true, true, true, true, false, false, true],
    #[true, true, false, true, true, true, true, false, false, true],
    #[true, true, true, false, true, true, true, false, false, true],
    #[true, true, true, true, false, true, true, false, false, true],
    #[true, true, true, true, true, false, true, false, false, true],
    #[true, true, true, true, true, true, false, true, false, true],
    #[false, false, false, false, false, false, true, false, true, false],
    #[false, false, false, false, false, false, false, true, false, true],
    #[true, true, true, true, true, true, true, false, true, false]]

private theorem k11t8p2_adjacency_row_0 : ∀ j : Fin 10,
    k11t8p2.graph.Adj 0 j ↔ adjacencyTableLookup k11t8p2_adjacencyTable 0 j.val = true := by decide

private theorem k11t8p2_adjacency_row_1 : ∀ j : Fin 10,
    k11t8p2.graph.Adj 1 j ↔ adjacencyTableLookup k11t8p2_adjacencyTable 1 j.val = true := by decide

private theorem k11t8p2_adjacency_row_2 : ∀ j : Fin 10,
    k11t8p2.graph.Adj 2 j ↔ adjacencyTableLookup k11t8p2_adjacencyTable 2 j.val = true := by decide

private theorem k11t8p2_adjacency_row_3 : ∀ j : Fin 10,
    k11t8p2.graph.Adj 3 j ↔ adjacencyTableLookup k11t8p2_adjacencyTable 3 j.val = true := by decide

private theorem k11t8p2_adjacency_row_4 : ∀ j : Fin 10,
    k11t8p2.graph.Adj 4 j ↔ adjacencyTableLookup k11t8p2_adjacencyTable 4 j.val = true := by decide

private theorem k11t8p2_adjacency_row_5 : ∀ j : Fin 10,
    k11t8p2.graph.Adj 5 j ↔ adjacencyTableLookup k11t8p2_adjacencyTable 5 j.val = true := by decide

private theorem k11t8p2_adjacency_row_6 : ∀ j : Fin 10,
    k11t8p2.graph.Adj 6 j ↔ adjacencyTableLookup k11t8p2_adjacencyTable 6 j.val = true := by decide

private theorem k11t8p2_adjacency_row_7 : ∀ j : Fin 10,
    k11t8p2.graph.Adj 7 j ↔ adjacencyTableLookup k11t8p2_adjacencyTable 7 j.val = true := by decide

private theorem k11t8p2_adjacency_row_8 : ∀ j : Fin 10,
    k11t8p2.graph.Adj 8 j ↔ adjacencyTableLookup k11t8p2_adjacencyTable 8 j.val = true := by decide

private theorem k11t8p2_adjacency_row_9 : ∀ j : Fin 10,
    k11t8p2.graph.Adj 9 j ↔ adjacencyTableLookup k11t8p2_adjacencyTable 9 j.val = true := by decide

private theorem k11t8p2_adjacency_eq : ∀ i j : Fin 10,
    k11t8p2.graph.Adj i j ↔ adjacencyTableLookup k11t8p2_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t8p2_adjacency_row_0 j

  · exact k11t8p2_adjacency_row_1 j

  · exact k11t8p2_adjacency_row_2 j

  · exact k11t8p2_adjacency_row_3 j

  · exact k11t8p2_adjacency_row_4 j

  · exact k11t8p2_adjacency_row_5 j

  · exact k11t8p2_adjacency_row_6 j

  · exact k11t8p2_adjacency_row_7 j

  · exact k11t8p2_adjacency_row_8 j

  · exact k11t8p2_adjacency_row_9 j

private def k11t8p2_tableGraph : SimpleGraph (Fin 10) :=
  adjacencyTableGraph k11t8p2.graph k11t8p2_adjacencyTable k11t8p2_adjacency_eq

private instance k11t8p2_tableGraph_decidableAdj :
    DecidableRel k11t8p2_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t8p2_adjacencyTable i.val j.val = true))

private theorem k11t8p2_tableGraph_eq : k11t8p2_tableGraph = k11t8p2.graph :=
  adjacencyTableGraph_eq k11t8p2.graph k11t8p2_adjacencyTable k11t8p2_adjacency_eq

private def k11t8p2_state_0 : ForbiddenMatrix 10 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 7, Finset.Icc 1 8, ∅, ∅],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 7, Finset.Icc 1 8, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 7, Finset.Icc 1 8, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 7, Finset.Icc 1 8, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 8, Finset.Icc 1 8, Finset.Icc 1 8, Finset.Icc 1 8, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t8p2_decode_entry_0 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_1 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_2 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_3 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_4 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_5 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p2_decode_entry_6 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p2_decode_entry_7 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_8 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_9 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_10 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_11 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p2_decode_entry_12 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p2_decode_entry_13 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_14 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_15 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_16 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p2_decode_entry_17 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p2_decode_entry_18 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_19 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p2_decode_entry_20 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p2_decode_entry_21 : decode 12 510 = Finset.Icc 1 8 := by decide

private def k11t8p2_mask_entries_0 : List (TemplateData (Fin 10) × ℕ) := [(⟨0, 1, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨0, 2, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨0, 3, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨0, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨0, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨0, 6, [], [], [7, 8, 9], 1, 7⟩, 254), (⟨0, 7, [], [], [8, 9], 1, 8⟩, 510), (⟨1, 2, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨1, 3, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨1, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨1, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨1, 6, [], [], [7, 8, 9], 1, 7⟩, 254), (⟨1, 7, [], [], [8, 9], 1, 8⟩, 510), (⟨2, 3, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨2, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨2, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨2, 6, [], [], [7, 8, 9], 1, 7⟩, 254), (⟨2, 7, [], [], [8, 9], 1, 8⟩, 510), (⟨3, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨3, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩, 126), (⟨3, 6, [], [], [7, 8, 9], 1, 7⟩, 254), (⟨3, 7, [], [], [8, 9], 1, 8⟩, 510)]

private theorem k11t8p2_decode_entries_0 : ∀ Tb ∈ k11t8p2_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t8p2_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p2_decode_entry_0, k11t8p2_decode_entry_1, k11t8p2_decode_entry_2, k11t8p2_decode_entry_3, k11t8p2_decode_entry_4, k11t8p2_decode_entry_5, k11t8p2_decode_entry_6, k11t8p2_decode_entry_7, k11t8p2_decode_entry_8, k11t8p2_decode_entry_9, k11t8p2_decode_entry_10, k11t8p2_decode_entry_11, k11t8p2_decode_entry_12, k11t8p2_decode_entry_13, k11t8p2_decode_entry_14, k11t8p2_decode_entry_15, k11t8p2_decode_entry_16, k11t8p2_decode_entry_17, k11t8p2_decode_entry_18, k11t8p2_decode_entry_19, k11t8p2_decode_entry_20, k11t8p2_decode_entry_21⟩

private def k11t8p2_mask_block_0 : Fin 10 → Fin 10 → ℕ :=
  fun i j => ((#[#[0, 126, 126, 126, 126, 126, 254, 510, 0, 0],
    #[126, 0, 126, 126, 126, 126, 254, 510, 0, 0],
    #[126, 126, 0, 126, 126, 126, 254, 510, 0, 0],
    #[126, 126, 126, 0, 126, 126, 254, 510, 0, 0],
    #[126, 126, 126, 126, 0, 0, 0, 0, 0, 0],
    #[126, 126, 126, 126, 0, 0, 0, 0, 0, 0],
    #[254, 254, 254, 254, 0, 0, 0, 0, 0, 0],
    #[510, 510, 510, 510, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p2_mask_block_0_eq_row_0 : ∀ j : Fin 10, (templateMaskMatrix k11t8p2_mask_entries_0) 0 j = k11t8p2_mask_block_0 0 j := by decide

private theorem k11t8p2_mask_block_0_eq_row_1 : ∀ j : Fin 10, (templateMaskMatrix k11t8p2_mask_entries_0) 1 j = k11t8p2_mask_block_0 1 j := by decide

private theorem k11t8p2_mask_block_0_eq_row_2 : ∀ j : Fin 10, (templateMaskMatrix k11t8p2_mask_entries_0) 2 j = k11t8p2_mask_block_0 2 j := by decide

private theorem k11t8p2_mask_block_0_eq_row_3 : ∀ j : Fin 10, (templateMaskMatrix k11t8p2_mask_entries_0) 3 j = k11t8p2_mask_block_0 3 j := by decide

private theorem k11t8p2_mask_block_0_eq_row_4 : ∀ j : Fin 10, (templateMaskMatrix k11t8p2_mask_entries_0) 4 j = k11t8p2_mask_block_0 4 j := by decide

private theorem k11t8p2_mask_block_0_eq_row_5 : ∀ j : Fin 10, (templateMaskMatrix k11t8p2_mask_entries_0) 5 j = k11t8p2_mask_block_0 5 j := by decide

private theorem k11t8p2_mask_block_0_eq_row_6 : ∀ j : Fin 10, (templateMaskMatrix k11t8p2_mask_entries_0) 6 j = k11t8p2_mask_block_0 6 j := by decide

private theorem k11t8p2_mask_block_0_eq_row_7 : ∀ j : Fin 10, (templateMaskMatrix k11t8p2_mask_entries_0) 7 j = k11t8p2_mask_block_0 7 j := by decide

private theorem k11t8p2_mask_block_0_eq_row_8 : ∀ j : Fin 10, (templateMaskMatrix k11t8p2_mask_entries_0) 8 j = k11t8p2_mask_block_0 8 j := by decide

private theorem k11t8p2_mask_block_0_eq_row_9 : ∀ j : Fin 10, (templateMaskMatrix k11t8p2_mask_entries_0) 9 j = k11t8p2_mask_block_0 9 j := by decide

private theorem k11t8p2_mask_block_0_eq : (templateMaskMatrix k11t8p2_mask_entries_0) = k11t8p2_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t8p2_mask_block_0_eq_row_0 j

  · exact k11t8p2_mask_block_0_eq_row_1 j

  · exact k11t8p2_mask_block_0_eq_row_2 j

  · exact k11t8p2_mask_block_0_eq_row_3 j

  · exact k11t8p2_mask_block_0_eq_row_4 j

  · exact k11t8p2_mask_block_0_eq_row_5 j

  · exact k11t8p2_mask_block_0_eq_row_6 j

  · exact k11t8p2_mask_block_0_eq_row_7 j

  · exact k11t8p2_mask_block_0_eq_row_8 j

  · exact k11t8p2_mask_block_0_eq_row_9 j

private def k11t8p2_mask_entries : List (TemplateData (Fin 10) × ℕ) := k11t8p2_mask_entries_0

private theorem k11t8p2_decode_entries : ∀ Tb ∈ k11t8p2_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t8p2_decode_entries_0

private theorem k11t8p2_mask_entries_map : k11t8p2_mask_entries.map Prod.fst = k11t8p2.templates := by rfl

private def k11t8p2_template_mask : Fin 10 → Fin 10 → ℕ :=
  fun i j => ((#[#[0, 126, 126, 126, 126, 126, 254, 510, 0, 0],
    #[126, 0, 126, 126, 126, 126, 254, 510, 0, 0],
    #[126, 126, 0, 126, 126, 126, 254, 510, 0, 0],
    #[126, 126, 126, 0, 126, 126, 254, 510, 0, 0],
    #[126, 126, 126, 126, 0, 0, 0, 0, 0, 0],
    #[126, 126, 126, 126, 0, 0, 0, 0, 0, 0],
    #[254, 254, 254, 254, 0, 0, 0, 0, 0, 0],
    #[510, 510, 510, 510, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p2_mask_merged_eq_row_0 : ∀ j : Fin 10, (fun i j => k11t8p2_mask_block_0 i j) 0 j = k11t8p2_template_mask 0 j := by decide

private theorem k11t8p2_mask_merged_eq_row_1 : ∀ j : Fin 10, (fun i j => k11t8p2_mask_block_0 i j) 1 j = k11t8p2_template_mask 1 j := by decide

private theorem k11t8p2_mask_merged_eq_row_2 : ∀ j : Fin 10, (fun i j => k11t8p2_mask_block_0 i j) 2 j = k11t8p2_template_mask 2 j := by decide

private theorem k11t8p2_mask_merged_eq_row_3 : ∀ j : Fin 10, (fun i j => k11t8p2_mask_block_0 i j) 3 j = k11t8p2_template_mask 3 j := by decide

private theorem k11t8p2_mask_merged_eq_row_4 : ∀ j : Fin 10, (fun i j => k11t8p2_mask_block_0 i j) 4 j = k11t8p2_template_mask 4 j := by decide

private theorem k11t8p2_mask_merged_eq_row_5 : ∀ j : Fin 10, (fun i j => k11t8p2_mask_block_0 i j) 5 j = k11t8p2_template_mask 5 j := by decide

private theorem k11t8p2_mask_merged_eq_row_6 : ∀ j : Fin 10, (fun i j => k11t8p2_mask_block_0 i j) 6 j = k11t8p2_template_mask 6 j := by decide

private theorem k11t8p2_mask_merged_eq_row_7 : ∀ j : Fin 10, (fun i j => k11t8p2_mask_block_0 i j) 7 j = k11t8p2_template_mask 7 j := by decide

private theorem k11t8p2_mask_merged_eq_row_8 : ∀ j : Fin 10, (fun i j => k11t8p2_mask_block_0 i j) 8 j = k11t8p2_template_mask 8 j := by decide

private theorem k11t8p2_mask_merged_eq_row_9 : ∀ j : Fin 10, (fun i j => k11t8p2_mask_block_0 i j) 9 j = k11t8p2_template_mask 9 j := by decide

private theorem k11t8p2_mask_merged_eq : (fun i j => k11t8p2_mask_block_0 i j) = k11t8p2_template_mask := by
  funext i j
  fin_cases i

  · exact k11t8p2_mask_merged_eq_row_0 j

  · exact k11t8p2_mask_merged_eq_row_1 j

  · exact k11t8p2_mask_merged_eq_row_2 j

  · exact k11t8p2_mask_merged_eq_row_3 j

  · exact k11t8p2_mask_merged_eq_row_4 j

  · exact k11t8p2_mask_merged_eq_row_5 j

  · exact k11t8p2_mask_merged_eq_row_6 j

  · exact k11t8p2_mask_merged_eq_row_7 j

  · exact k11t8p2_mask_merged_eq_row_8 j

  · exact k11t8p2_mask_merged_eq_row_9 j

private theorem k11t8p2_template_mask_eq : templateMaskMatrix k11t8p2_mask_entries = k11t8p2_template_mask := by
  funext i j
  change templateMaskMatrix (k11t8p2_mask_entries_0) i j = _
  simp only [k11t8p2_mask_block_0_eq]
  exact congrFun (congrFun k11t8p2_mask_merged_eq i) j

private theorem k11t8p2_initial_decoded_eq_row_0 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p2_template_mask i j) ∪ requiredMatrix 11 k11t8p2.required i j) 0 j = k11t8p2_state_0 0 j := by decide

private theorem k11t8p2_initial_decoded_eq_row_1 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p2_template_mask i j) ∪ requiredMatrix 11 k11t8p2.required i j) 1 j = k11t8p2_state_0 1 j := by decide

private theorem k11t8p2_initial_decoded_eq_row_2 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p2_template_mask i j) ∪ requiredMatrix 11 k11t8p2.required i j) 2 j = k11t8p2_state_0 2 j := by decide

private theorem k11t8p2_initial_decoded_eq_row_3 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p2_template_mask i j) ∪ requiredMatrix 11 k11t8p2.required i j) 3 j = k11t8p2_state_0 3 j := by decide

private theorem k11t8p2_initial_decoded_eq_row_4 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p2_template_mask i j) ∪ requiredMatrix 11 k11t8p2.required i j) 4 j = k11t8p2_state_0 4 j := by decide

private theorem k11t8p2_initial_decoded_eq_row_5 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p2_template_mask i j) ∪ requiredMatrix 11 k11t8p2.required i j) 5 j = k11t8p2_state_0 5 j := by decide

private theorem k11t8p2_initial_decoded_eq_row_6 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p2_template_mask i j) ∪ requiredMatrix 11 k11t8p2.required i j) 6 j = k11t8p2_state_0 6 j := by decide

private theorem k11t8p2_initial_decoded_eq_row_7 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p2_template_mask i j) ∪ requiredMatrix 11 k11t8p2.required i j) 7 j = k11t8p2_state_0 7 j := by decide

private theorem k11t8p2_initial_decoded_eq_row_8 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p2_template_mask i j) ∪ requiredMatrix 11 k11t8p2.required i j) 8 j = k11t8p2_state_0 8 j := by decide

private theorem k11t8p2_initial_decoded_eq_row_9 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p2_template_mask i j) ∪ requiredMatrix 11 k11t8p2.required i j) 9 j = k11t8p2_state_0 9 j := by decide

private theorem k11t8p2_initial_decoded_eq : (fun i j => decode 12 (k11t8p2_template_mask i j) ∪ requiredMatrix 11 k11t8p2.required i j) = k11t8p2_state_0 := by
  funext i j
  fin_cases i

  · exact k11t8p2_initial_decoded_eq_row_0 j

  · exact k11t8p2_initial_decoded_eq_row_1 j

  · exact k11t8p2_initial_decoded_eq_row_2 j

  · exact k11t8p2_initial_decoded_eq_row_3 j

  · exact k11t8p2_initial_decoded_eq_row_4 j

  · exact k11t8p2_initial_decoded_eq_row_5 j

  · exact k11t8p2_initial_decoded_eq_row_6 j

  · exact k11t8p2_initial_decoded_eq_row_7 j

  · exact k11t8p2_initial_decoded_eq_row_8 j

  · exact k11t8p2_initial_decoded_eq_row_9 j

private theorem k11t8p2_initial_eq : k11t8p2.initialMatrix 11 = k11t8p2_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t8p2_mask_entries k11t8p2_decode_entries
  rw [k11t8p2_mask_entries_map, k11t8p2_template_mask_eq] at h
  funext i j
  change templateMatrix k11t8p2.templates i j ∪ requiredMatrix 11 k11t8p2.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t8p2_initial_decoded_eq i) j

private theorem k11t8p2_closure_0 : ClosureCheck k11t8p2.graph k11t8p2_state_0 11 8 [] := by trivial

private theorem k11t8p2_matrix_eq : k11t8p2.matrix 11 = k11t8p2_state_0 := by
  change closureMatrix (k11t8p2.initialMatrix 11) _ = _
  rw [k11t8p2_initial_eq]
  change closureMatrix k11t8p2_state_0 [] = _
  rfl

private theorem k11t8p2_part_0 : k11t8p2.chains.flatten = List.finRange _ := by decide

private theorem k11t8p2_part_1 : k11t8p2.chains.map List.length = ([[], [], [], [], [], [], [2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t8p2_part_2 : k11t8p2.chains.map (fun l => l.map (fun i => decide (i ∈ k11t8p2.clique))) = ([[], [], [], [], [], [], [2]] : List (List ℕ)).map profileMask := by decide

private theorem k11t8p2_templates_item_0 : (⟨0, 1, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_1 : (⟨0, 2, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_2 : (⟨0, 3, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_3 : (⟨0, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_4 : (⟨0, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_5 : (⟨0, 6, [], [], [7, 8, 9], 1, 7⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_6 : (⟨0, 7, [], [], [8, 9], 1, 8⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_7 : (⟨1, 2, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_8 : (⟨1, 3, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_9 : (⟨1, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_10 : (⟨1, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_11 : (⟨1, 6, [], [], [7, 8, 9], 1, 7⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_12 : (⟨1, 7, [], [], [8, 9], 1, 8⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_13 : (⟨2, 3, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_14 : (⟨2, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_15 : (⟨2, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_16 : (⟨2, 6, [], [], [7, 8, 9], 1, 7⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_17 : (⟨2, 7, [], [], [8, 9], 1, 8⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_18 : (⟨3, 4, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_19 : (⟨3, 5, [[6, 7, 8, 9]], [], [], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_20 : (⟨3, 6, [], [], [7, 8, 9], 1, 7⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_item_21 : (⟨3, 7, [], [], [8, 9], 1, 8⟩ : TemplateData (Fin 10)).Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p2_tableGraph_eq]
  decide

private theorem k11t8p2_templates_fast_block_0_check : ∀ T ∈ k11t8p2_mask_entries_0.map Prod.fst, T.Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t8p2_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p2_templates_item_0, k11t8p2_templates_item_1, k11t8p2_templates_item_2, k11t8p2_templates_item_3, k11t8p2_templates_item_4, k11t8p2_templates_item_5, k11t8p2_templates_item_6, k11t8p2_templates_item_7, k11t8p2_templates_item_8, k11t8p2_templates_item_9, k11t8p2_templates_item_10, k11t8p2_templates_item_11, k11t8p2_templates_item_12, k11t8p2_templates_item_13, k11t8p2_templates_item_14, k11t8p2_templates_item_15, k11t8p2_templates_item_16, k11t8p2_templates_item_17, k11t8p2_templates_item_18, k11t8p2_templates_item_19, k11t8p2_templates_item_20, k11t8p2_templates_item_21⟩

private theorem k11t8p2_part_3 : ∀ T ∈ k11t8p2.templates, T.Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t8p2_mask_entries_0.map Prod.fst), T.Check k11t8p2.graph k11t8p2.clique 11 (patternAmount ([[], [], [], [], [], [], [2]] : List (List ℕ))) (([[], [], [], [], [], [], [2]] : List (List ℕ)).map List.length).sum
  exact k11t8p2_templates_fast_block_0_check

private theorem k11t8p2_part_4 : ∀ p ∈ k11t8p2.required, p.Check k11t8p2.graph 11 := by decide

private theorem k11t8p2_part_5 : ClosureCheck k11t8p2.graph (k11t8p2.initialMatrix 11) 11 8 k11t8p2.closure := by
  rw [k11t8p2_initial_eq]
  exact k11t8p2_closure_0

private theorem k11t8p2_part_6 : k11t8p2.bad.Check k11t8p2.graph (k11t8p2.matrix 11) 11 8 := by
  rw [k11t8p2_matrix_eq]
  decide

theorem k11t8p2_check : k11t8p2.Check 11 8 [[], [], [], [], [], [], [2]] :=
  ⟨k11t8p2_part_0, k11t8p2_part_1, k11t8p2_part_2, k11t8p2_part_3, k11t8p2_part_4, k11t8p2_part_5, k11t8p2_part_6⟩
def k11t8p3 : LayoutCertificate 11 where
  chains := [[0], [1], [2], [3], [4], [5], [6, 7, 8, 9, 10]]
  clique := {0, 1, 2, 3, 4, 5, 6, 10}
  templates := [⟨0, 1, [], [], [], 4, 10⟩,
    ⟨0, 1, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨0, 2, [], [], [], 4, 10⟩,
    ⟨0, 2, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨0, 3, [], [], [], 4, 10⟩,
    ⟨0, 3, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨0, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨0, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨0, 6, [], [], [7, 8, 9, 10], 1, 6⟩,
    ⟨0, 7, [], [], [8, 9, 10], 1, 7⟩,
    ⟨0, 9, [], [], [8, 7, 6], 1, 7⟩,
    ⟨1, 2, [], [], [], 4, 10⟩,
    ⟨1, 2, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨1, 3, [], [], [], 4, 10⟩,
    ⟨1, 3, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨1, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨1, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨1, 6, [], [], [7, 8, 9, 10], 1, 6⟩,
    ⟨1, 7, [], [], [8, 9, 10], 1, 7⟩,
    ⟨1, 9, [], [], [8, 7, 6], 1, 7⟩,
    ⟨2, 3, [], [], [], 4, 10⟩,
    ⟨2, 3, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨2, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨2, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨2, 6, [], [], [7, 8, 9, 10], 1, 6⟩,
    ⟨2, 7, [], [], [8, 9, 10], 1, 7⟩,
    ⟨2, 9, [], [], [8, 7, 6], 1, 7⟩,
    ⟨3, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨3, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩,
    ⟨3, 6, [], [], [7, 8, 9, 10], 1, 6⟩,
    ⟨3, 7, [], [], [8, 9, 10], 1, 7⟩,
    ⟨3, 9, [], [], [8, 7, 6], 1, 7⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (2, 3), (3, 3)}⟩


private def k11t8p3_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, true, true, true, true, false, false, false, true],
    #[true, false, true, true, true, true, true, false, false, false, true],
    #[true, true, false, true, true, true, true, false, false, false, true],
    #[true, true, true, false, true, true, true, false, false, false, true],
    #[true, true, true, true, false, true, true, false, false, false, true],
    #[true, true, true, true, true, false, true, false, false, false, true],
    #[true, true, true, true, true, true, false, true, false, false, true],
    #[false, false, false, false, false, false, true, false, true, false, false],
    #[false, false, false, false, false, false, false, true, false, true, false],
    #[false, false, false, false, false, false, false, false, true, false, true],
    #[true, true, true, true, true, true, true, false, false, true, false]]

private theorem k11t8p3_adjacency_row_0 : ∀ j : Fin 11,
    k11t8p3.graph.Adj 0 j ↔ adjacencyTableLookup k11t8p3_adjacencyTable 0 j.val = true := by decide

private theorem k11t8p3_adjacency_row_1 : ∀ j : Fin 11,
    k11t8p3.graph.Adj 1 j ↔ adjacencyTableLookup k11t8p3_adjacencyTable 1 j.val = true := by decide

private theorem k11t8p3_adjacency_row_2 : ∀ j : Fin 11,
    k11t8p3.graph.Adj 2 j ↔ adjacencyTableLookup k11t8p3_adjacencyTable 2 j.val = true := by decide

private theorem k11t8p3_adjacency_row_3 : ∀ j : Fin 11,
    k11t8p3.graph.Adj 3 j ↔ adjacencyTableLookup k11t8p3_adjacencyTable 3 j.val = true := by decide

private theorem k11t8p3_adjacency_row_4 : ∀ j : Fin 11,
    k11t8p3.graph.Adj 4 j ↔ adjacencyTableLookup k11t8p3_adjacencyTable 4 j.val = true := by decide

private theorem k11t8p3_adjacency_row_5 : ∀ j : Fin 11,
    k11t8p3.graph.Adj 5 j ↔ adjacencyTableLookup k11t8p3_adjacencyTable 5 j.val = true := by decide

private theorem k11t8p3_adjacency_row_6 : ∀ j : Fin 11,
    k11t8p3.graph.Adj 6 j ↔ adjacencyTableLookup k11t8p3_adjacencyTable 6 j.val = true := by decide

private theorem k11t8p3_adjacency_row_7 : ∀ j : Fin 11,
    k11t8p3.graph.Adj 7 j ↔ adjacencyTableLookup k11t8p3_adjacencyTable 7 j.val = true := by decide

private theorem k11t8p3_adjacency_row_8 : ∀ j : Fin 11,
    k11t8p3.graph.Adj 8 j ↔ adjacencyTableLookup k11t8p3_adjacencyTable 8 j.val = true := by decide

private theorem k11t8p3_adjacency_row_9 : ∀ j : Fin 11,
    k11t8p3.graph.Adj 9 j ↔ adjacencyTableLookup k11t8p3_adjacencyTable 9 j.val = true := by decide

private theorem k11t8p3_adjacency_row_10 : ∀ j : Fin 11,
    k11t8p3.graph.Adj 10 j ↔ adjacencyTableLookup k11t8p3_adjacencyTable 10 j.val = true := by decide

private theorem k11t8p3_adjacency_eq : ∀ i j : Fin 11,
    k11t8p3.graph.Adj i j ↔ adjacencyTableLookup k11t8p3_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t8p3_adjacency_row_0 j

  · exact k11t8p3_adjacency_row_1 j

  · exact k11t8p3_adjacency_row_2 j

  · exact k11t8p3_adjacency_row_3 j

  · exact k11t8p3_adjacency_row_4 j

  · exact k11t8p3_adjacency_row_5 j

  · exact k11t8p3_adjacency_row_6 j

  · exact k11t8p3_adjacency_row_7 j

  · exact k11t8p3_adjacency_row_8 j

  · exact k11t8p3_adjacency_row_9 j

  · exact k11t8p3_adjacency_row_10 j

private def k11t8p3_tableGraph : SimpleGraph (Fin 11) :=
  adjacencyTableGraph k11t8p3.graph k11t8p3_adjacencyTable k11t8p3_adjacency_eq

private instance k11t8p3_tableGraph_decidableAdj :
    DecidableRel k11t8p3_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t8p3_adjacencyTable i.val j.val = true))

private theorem k11t8p3_tableGraph_eq : k11t8p3_tableGraph = k11t8p3.graph :=
  adjacencyTableGraph_eq k11t8p3.graph k11t8p3_adjacencyTable k11t8p3_adjacency_eq

private def k11t8p3_state_0 : ForbiddenMatrix 11 :=
  fun i j => ((#[#[∅, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 6, Finset.Icc 1 7, ∅, Finset.Icc 1 7, ∅],
    #[Finset.Icc 1 10, ∅, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 6, Finset.Icc 1 7, ∅, Finset.Icc 1 7, ∅],
    #[Finset.Icc 1 10, Finset.Icc 1 10, ∅, Finset.Icc 1 10, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 6, Finset.Icc 1 7, ∅, Finset.Icc 1 7, ∅],
    #[Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, ∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 6, Finset.Icc 1 7, ∅, Finset.Icc 1 7, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t8p3_decode_entry_0 : decode 12 2032 = Finset.Icc 4 10 := by decide

private theorem k11t8p3_decode_entry_1 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_2 : decode 12 2032 = Finset.Icc 4 10 := by decide

private theorem k11t8p3_decode_entry_3 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_4 : decode 12 2032 = Finset.Icc 4 10 := by decide

private theorem k11t8p3_decode_entry_5 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_6 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_7 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_8 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p3_decode_entry_9 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p3_decode_entry_10 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p3_decode_entry_11 : decode 12 2032 = Finset.Icc 4 10 := by decide

private theorem k11t8p3_decode_entry_12 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_13 : decode 12 2032 = Finset.Icc 4 10 := by decide

private theorem k11t8p3_decode_entry_14 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_15 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_16 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_17 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p3_decode_entry_18 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p3_decode_entry_19 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p3_decode_entry_20 : decode 12 2032 = Finset.Icc 4 10 := by decide

private theorem k11t8p3_decode_entry_21 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_22 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_23 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_24 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p3_decode_entry_25 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p3_decode_entry_26 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p3_decode_entry_27 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_28 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p3_decode_entry_29 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p3_decode_entry_30 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p3_decode_entry_31 : decode 12 254 = Finset.Icc 1 7 := by decide

private def k11t8p3_mask_entries_0 : List (TemplateData (Fin 11) × ℕ) := [(⟨0, 1, [], [], [], 4, 10⟩, 2032), (⟨0, 1, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨0, 2, [], [], [], 4, 10⟩, 2032), (⟨0, 2, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨0, 3, [], [], [], 4, 10⟩, 2032), (⟨0, 3, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨0, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨0, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨0, 6, [], [], [7, 8, 9, 10], 1, 6⟩, 126), (⟨0, 7, [], [], [8, 9, 10], 1, 7⟩, 254), (⟨0, 9, [], [], [8, 7, 6], 1, 7⟩, 254), (⟨1, 2, [], [], [], 4, 10⟩, 2032), (⟨1, 2, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨1, 3, [], [], [], 4, 10⟩, 2032), (⟨1, 3, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨1, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨1, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨1, 6, [], [], [7, 8, 9, 10], 1, 6⟩, 126), (⟨1, 7, [], [], [8, 9, 10], 1, 7⟩, 254), (⟨1, 9, [], [], [8, 7, 6], 1, 7⟩, 254), (⟨2, 3, [], [], [], 4, 10⟩, 2032), (⟨2, 3, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨2, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨2, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨2, 6, [], [], [7, 8, 9, 10], 1, 6⟩, 126), (⟨2, 7, [], [], [8, 9, 10], 1, 7⟩, 254), (⟨2, 9, [], [], [8, 7, 6], 1, 7⟩, 254), (⟨3, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨3, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩, 62), (⟨3, 6, [], [], [7, 8, 9, 10], 1, 6⟩, 126), (⟨3, 7, [], [], [8, 9, 10], 1, 7⟩, 254), (⟨3, 9, [], [], [8, 7, 6], 1, 7⟩, 254)]

private theorem k11t8p3_decode_entries_0 : ∀ Tb ∈ k11t8p3_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t8p3_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p3_decode_entry_0, k11t8p3_decode_entry_1, k11t8p3_decode_entry_2, k11t8p3_decode_entry_3, k11t8p3_decode_entry_4, k11t8p3_decode_entry_5, k11t8p3_decode_entry_6, k11t8p3_decode_entry_7, k11t8p3_decode_entry_8, k11t8p3_decode_entry_9, k11t8p3_decode_entry_10, k11t8p3_decode_entry_11, k11t8p3_decode_entry_12, k11t8p3_decode_entry_13, k11t8p3_decode_entry_14, k11t8p3_decode_entry_15, k11t8p3_decode_entry_16, k11t8p3_decode_entry_17, k11t8p3_decode_entry_18, k11t8p3_decode_entry_19, k11t8p3_decode_entry_20, k11t8p3_decode_entry_21, k11t8p3_decode_entry_22, k11t8p3_decode_entry_23, k11t8p3_decode_entry_24, k11t8p3_decode_entry_25, k11t8p3_decode_entry_26, k11t8p3_decode_entry_27, k11t8p3_decode_entry_28, k11t8p3_decode_entry_29, k11t8p3_decode_entry_30, k11t8p3_decode_entry_31⟩

private def k11t8p3_mask_block_0 : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 2046, 2046, 2046, 62, 62, 126, 254, 0, 254, 0],
    #[2046, 0, 2046, 2046, 62, 62, 126, 254, 0, 254, 0],
    #[2046, 2046, 0, 2046, 62, 62, 126, 254, 0, 254, 0],
    #[2046, 2046, 2046, 0, 62, 62, 126, 254, 0, 254, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0, 0],
    #[126, 126, 126, 126, 0, 0, 0, 0, 0, 0, 0],
    #[254, 254, 254, 254, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[254, 254, 254, 254, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p3_mask_block_0_eq_row_0 : ∀ j : Fin 11, (templateMaskMatrix k11t8p3_mask_entries_0) 0 j = k11t8p3_mask_block_0 0 j := by decide

private theorem k11t8p3_mask_block_0_eq_row_1 : ∀ j : Fin 11, (templateMaskMatrix k11t8p3_mask_entries_0) 1 j = k11t8p3_mask_block_0 1 j := by decide

private theorem k11t8p3_mask_block_0_eq_row_2 : ∀ j : Fin 11, (templateMaskMatrix k11t8p3_mask_entries_0) 2 j = k11t8p3_mask_block_0 2 j := by decide

private theorem k11t8p3_mask_block_0_eq_row_3 : ∀ j : Fin 11, (templateMaskMatrix k11t8p3_mask_entries_0) 3 j = k11t8p3_mask_block_0 3 j := by decide

private theorem k11t8p3_mask_block_0_eq_row_4 : ∀ j : Fin 11, (templateMaskMatrix k11t8p3_mask_entries_0) 4 j = k11t8p3_mask_block_0 4 j := by decide

private theorem k11t8p3_mask_block_0_eq_row_5 : ∀ j : Fin 11, (templateMaskMatrix k11t8p3_mask_entries_0) 5 j = k11t8p3_mask_block_0 5 j := by decide

private theorem k11t8p3_mask_block_0_eq_row_6 : ∀ j : Fin 11, (templateMaskMatrix k11t8p3_mask_entries_0) 6 j = k11t8p3_mask_block_0 6 j := by decide

private theorem k11t8p3_mask_block_0_eq_row_7 : ∀ j : Fin 11, (templateMaskMatrix k11t8p3_mask_entries_0) 7 j = k11t8p3_mask_block_0 7 j := by decide

private theorem k11t8p3_mask_block_0_eq_row_8 : ∀ j : Fin 11, (templateMaskMatrix k11t8p3_mask_entries_0) 8 j = k11t8p3_mask_block_0 8 j := by decide

private theorem k11t8p3_mask_block_0_eq_row_9 : ∀ j : Fin 11, (templateMaskMatrix k11t8p3_mask_entries_0) 9 j = k11t8p3_mask_block_0 9 j := by decide

private theorem k11t8p3_mask_block_0_eq_row_10 : ∀ j : Fin 11, (templateMaskMatrix k11t8p3_mask_entries_0) 10 j = k11t8p3_mask_block_0 10 j := by decide

private theorem k11t8p3_mask_block_0_eq : (templateMaskMatrix k11t8p3_mask_entries_0) = k11t8p3_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t8p3_mask_block_0_eq_row_0 j

  · exact k11t8p3_mask_block_0_eq_row_1 j

  · exact k11t8p3_mask_block_0_eq_row_2 j

  · exact k11t8p3_mask_block_0_eq_row_3 j

  · exact k11t8p3_mask_block_0_eq_row_4 j

  · exact k11t8p3_mask_block_0_eq_row_5 j

  · exact k11t8p3_mask_block_0_eq_row_6 j

  · exact k11t8p3_mask_block_0_eq_row_7 j

  · exact k11t8p3_mask_block_0_eq_row_8 j

  · exact k11t8p3_mask_block_0_eq_row_9 j

  · exact k11t8p3_mask_block_0_eq_row_10 j

private def k11t8p3_mask_entries : List (TemplateData (Fin 11) × ℕ) := k11t8p3_mask_entries_0

private theorem k11t8p3_decode_entries : ∀ Tb ∈ k11t8p3_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t8p3_decode_entries_0

private theorem k11t8p3_mask_entries_map : k11t8p3_mask_entries.map Prod.fst = k11t8p3.templates := by rfl

private def k11t8p3_template_mask : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 2046, 2046, 2046, 62, 62, 126, 254, 0, 254, 0],
    #[2046, 0, 2046, 2046, 62, 62, 126, 254, 0, 254, 0],
    #[2046, 2046, 0, 2046, 62, 62, 126, 254, 0, 254, 0],
    #[2046, 2046, 2046, 0, 62, 62, 126, 254, 0, 254, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0, 0],
    #[126, 126, 126, 126, 0, 0, 0, 0, 0, 0, 0],
    #[254, 254, 254, 254, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[254, 254, 254, 254, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p3_mask_merged_eq_row_0 : ∀ j : Fin 11, (fun i j => k11t8p3_mask_block_0 i j) 0 j = k11t8p3_template_mask 0 j := by decide

private theorem k11t8p3_mask_merged_eq_row_1 : ∀ j : Fin 11, (fun i j => k11t8p3_mask_block_0 i j) 1 j = k11t8p3_template_mask 1 j := by decide

private theorem k11t8p3_mask_merged_eq_row_2 : ∀ j : Fin 11, (fun i j => k11t8p3_mask_block_0 i j) 2 j = k11t8p3_template_mask 2 j := by decide

private theorem k11t8p3_mask_merged_eq_row_3 : ∀ j : Fin 11, (fun i j => k11t8p3_mask_block_0 i j) 3 j = k11t8p3_template_mask 3 j := by decide

private theorem k11t8p3_mask_merged_eq_row_4 : ∀ j : Fin 11, (fun i j => k11t8p3_mask_block_0 i j) 4 j = k11t8p3_template_mask 4 j := by decide

private theorem k11t8p3_mask_merged_eq_row_5 : ∀ j : Fin 11, (fun i j => k11t8p3_mask_block_0 i j) 5 j = k11t8p3_template_mask 5 j := by decide

private theorem k11t8p3_mask_merged_eq_row_6 : ∀ j : Fin 11, (fun i j => k11t8p3_mask_block_0 i j) 6 j = k11t8p3_template_mask 6 j := by decide

private theorem k11t8p3_mask_merged_eq_row_7 : ∀ j : Fin 11, (fun i j => k11t8p3_mask_block_0 i j) 7 j = k11t8p3_template_mask 7 j := by decide

private theorem k11t8p3_mask_merged_eq_row_8 : ∀ j : Fin 11, (fun i j => k11t8p3_mask_block_0 i j) 8 j = k11t8p3_template_mask 8 j := by decide

private theorem k11t8p3_mask_merged_eq_row_9 : ∀ j : Fin 11, (fun i j => k11t8p3_mask_block_0 i j) 9 j = k11t8p3_template_mask 9 j := by decide

private theorem k11t8p3_mask_merged_eq_row_10 : ∀ j : Fin 11, (fun i j => k11t8p3_mask_block_0 i j) 10 j = k11t8p3_template_mask 10 j := by decide

private theorem k11t8p3_mask_merged_eq : (fun i j => k11t8p3_mask_block_0 i j) = k11t8p3_template_mask := by
  funext i j
  fin_cases i

  · exact k11t8p3_mask_merged_eq_row_0 j

  · exact k11t8p3_mask_merged_eq_row_1 j

  · exact k11t8p3_mask_merged_eq_row_2 j

  · exact k11t8p3_mask_merged_eq_row_3 j

  · exact k11t8p3_mask_merged_eq_row_4 j

  · exact k11t8p3_mask_merged_eq_row_5 j

  · exact k11t8p3_mask_merged_eq_row_6 j

  · exact k11t8p3_mask_merged_eq_row_7 j

  · exact k11t8p3_mask_merged_eq_row_8 j

  · exact k11t8p3_mask_merged_eq_row_9 j

  · exact k11t8p3_mask_merged_eq_row_10 j

private theorem k11t8p3_template_mask_eq : templateMaskMatrix k11t8p3_mask_entries = k11t8p3_template_mask := by
  funext i j
  change templateMaskMatrix (k11t8p3_mask_entries_0) i j = _
  simp only [k11t8p3_mask_block_0_eq]
  exact congrFun (congrFun k11t8p3_mask_merged_eq i) j

private theorem k11t8p3_initial_decoded_eq_row_0 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) 0 j = k11t8p3_state_0 0 j := by decide

private theorem k11t8p3_initial_decoded_eq_row_1 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) 1 j = k11t8p3_state_0 1 j := by decide

private theorem k11t8p3_initial_decoded_eq_row_2 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) 2 j = k11t8p3_state_0 2 j := by decide

private theorem k11t8p3_initial_decoded_eq_row_3 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) 3 j = k11t8p3_state_0 3 j := by decide

private theorem k11t8p3_initial_decoded_eq_row_4 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) 4 j = k11t8p3_state_0 4 j := by decide

private theorem k11t8p3_initial_decoded_eq_row_5 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) 5 j = k11t8p3_state_0 5 j := by decide

private theorem k11t8p3_initial_decoded_eq_row_6 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) 6 j = k11t8p3_state_0 6 j := by decide

private theorem k11t8p3_initial_decoded_eq_row_7 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) 7 j = k11t8p3_state_0 7 j := by decide

private theorem k11t8p3_initial_decoded_eq_row_8 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) 8 j = k11t8p3_state_0 8 j := by decide

private theorem k11t8p3_initial_decoded_eq_row_9 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) 9 j = k11t8p3_state_0 9 j := by decide

private theorem k11t8p3_initial_decoded_eq_row_10 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) 10 j = k11t8p3_state_0 10 j := by decide

private theorem k11t8p3_initial_decoded_eq : (fun i j => decode 12 (k11t8p3_template_mask i j) ∪ requiredMatrix 11 k11t8p3.required i j) = k11t8p3_state_0 := by
  funext i j
  fin_cases i

  · exact k11t8p3_initial_decoded_eq_row_0 j

  · exact k11t8p3_initial_decoded_eq_row_1 j

  · exact k11t8p3_initial_decoded_eq_row_2 j

  · exact k11t8p3_initial_decoded_eq_row_3 j

  · exact k11t8p3_initial_decoded_eq_row_4 j

  · exact k11t8p3_initial_decoded_eq_row_5 j

  · exact k11t8p3_initial_decoded_eq_row_6 j

  · exact k11t8p3_initial_decoded_eq_row_7 j

  · exact k11t8p3_initial_decoded_eq_row_8 j

  · exact k11t8p3_initial_decoded_eq_row_9 j

  · exact k11t8p3_initial_decoded_eq_row_10 j

private theorem k11t8p3_initial_eq : k11t8p3.initialMatrix 11 = k11t8p3_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t8p3_mask_entries k11t8p3_decode_entries
  rw [k11t8p3_mask_entries_map, k11t8p3_template_mask_eq] at h
  funext i j
  change templateMatrix k11t8p3.templates i j ∪ requiredMatrix 11 k11t8p3.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t8p3_initial_decoded_eq i) j

private theorem k11t8p3_closure_0 : ClosureCheck k11t8p3.graph k11t8p3_state_0 11 8 [] := by trivial

private theorem k11t8p3_matrix_eq : k11t8p3.matrix 11 = k11t8p3_state_0 := by
  change closureMatrix (k11t8p3.initialMatrix 11) _ = _
  rw [k11t8p3_initial_eq]
  change closureMatrix k11t8p3_state_0 [] = _
  rfl

private theorem k11t8p3_part_0 : k11t8p3.chains.flatten = List.finRange _ := by decide

private theorem k11t8p3_part_1 : k11t8p3.chains.map List.length = ([[], [], [], [], [], [], [3]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t8p3_part_2 : k11t8p3.chains.map (fun l => l.map (fun i => decide (i ∈ k11t8p3.clique))) = ([[], [], [], [], [], [], [3]] : List (List ℕ)).map profileMask := by decide

private theorem k11t8p3_templates_item_0 : (⟨0, 1, [], [], [], 4, 10⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_1 : (⟨0, 1, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_2 : (⟨0, 2, [], [], [], 4, 10⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_3 : (⟨0, 2, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_4 : (⟨0, 3, [], [], [], 4, 10⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_5 : (⟨0, 3, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_6 : (⟨0, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_7 : (⟨0, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_8 : (⟨0, 6, [], [], [7, 8, 9, 10], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_9 : (⟨0, 7, [], [], [8, 9, 10], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_10 : (⟨0, 9, [], [], [8, 7, 6], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_11 : (⟨1, 2, [], [], [], 4, 10⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_12 : (⟨1, 2, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_13 : (⟨1, 3, [], [], [], 4, 10⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_14 : (⟨1, 3, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_15 : (⟨1, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_16 : (⟨1, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_17 : (⟨1, 6, [], [], [7, 8, 9, 10], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_18 : (⟨1, 7, [], [], [8, 9, 10], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_19 : (⟨1, 9, [], [], [8, 7, 6], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_20 : (⟨2, 3, [], [], [], 4, 10⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_21 : (⟨2, 3, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_22 : (⟨2, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_23 : (⟨2, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_24 : (⟨2, 6, [], [], [7, 8, 9, 10], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_25 : (⟨2, 7, [], [], [8, 9, 10], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_26 : (⟨2, 9, [], [], [8, 7, 6], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_27 : (⟨3, 4, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_28 : (⟨3, 5, [[6, 7, 8, 9, 10]], [], [], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_29 : (⟨3, 6, [], [], [7, 8, 9, 10], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_30 : (⟨3, 7, [], [], [8, 9, 10], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_item_31 : (⟨3, 9, [], [], [8, 7, 6], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p3_tableGraph_eq]
  decide

private theorem k11t8p3_templates_fast_block_0_check : ∀ T ∈ k11t8p3_mask_entries_0.map Prod.fst, T.Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t8p3_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p3_templates_item_0, k11t8p3_templates_item_1, k11t8p3_templates_item_2, k11t8p3_templates_item_3, k11t8p3_templates_item_4, k11t8p3_templates_item_5, k11t8p3_templates_item_6, k11t8p3_templates_item_7, k11t8p3_templates_item_8, k11t8p3_templates_item_9, k11t8p3_templates_item_10, k11t8p3_templates_item_11, k11t8p3_templates_item_12, k11t8p3_templates_item_13, k11t8p3_templates_item_14, k11t8p3_templates_item_15, k11t8p3_templates_item_16, k11t8p3_templates_item_17, k11t8p3_templates_item_18, k11t8p3_templates_item_19, k11t8p3_templates_item_20, k11t8p3_templates_item_21, k11t8p3_templates_item_22, k11t8p3_templates_item_23, k11t8p3_templates_item_24, k11t8p3_templates_item_25, k11t8p3_templates_item_26, k11t8p3_templates_item_27, k11t8p3_templates_item_28, k11t8p3_templates_item_29, k11t8p3_templates_item_30, k11t8p3_templates_item_31⟩

private theorem k11t8p3_part_3 : ∀ T ∈ k11t8p3.templates, T.Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t8p3_mask_entries_0.map Prod.fst), T.Check k11t8p3.graph k11t8p3.clique 11 (patternAmount ([[], [], [], [], [], [], [3]] : List (List ℕ))) (([[], [], [], [], [], [], [3]] : List (List ℕ)).map List.length).sum
  exact k11t8p3_templates_fast_block_0_check

private theorem k11t8p3_part_4 : ∀ p ∈ k11t8p3.required, p.Check k11t8p3.graph 11 := by decide

private theorem k11t8p3_part_5 : ClosureCheck k11t8p3.graph (k11t8p3.initialMatrix 11) 11 8 k11t8p3.closure := by
  rw [k11t8p3_initial_eq]
  exact k11t8p3_closure_0

private theorem k11t8p3_part_6 : k11t8p3.bad.Check k11t8p3.graph (k11t8p3.matrix 11) 11 8 := by
  rw [k11t8p3_matrix_eq]
  decide

theorem k11t8p3_check : k11t8p3.Check 11 8 [[], [], [], [], [], [], [3]] :=
  ⟨k11t8p3_part_0, k11t8p3_part_1, k11t8p3_part_2, k11t8p3_part_3, k11t8p3_part_4, k11t8p3_part_5, k11t8p3_part_6⟩
def k11t8p4 : LayoutCertificate 10 where
  chains := [[0], [1], [2], [3], [4], [5, 6, 7, 8, 9]]
  clique := {0, 1, 2, 3, 4, 5, 7, 9}
  templates := [⟨0, 1, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩,
    ⟨0, 2, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩,
    ⟨0, 3, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩,
    ⟨0, 4, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩,
    ⟨0, 5, [], [], [6, 7, 8, 9], 1, 6⟩,
    ⟨0, 6, [], [], [5], 1, 9⟩,
    ⟨0, 8, [], [], [7], 1, 9⟩,
    ⟨1, 2, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩,
    ⟨1, 3, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩,
    ⟨1, 4, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩,
    ⟨1, 5, [], [], [6, 7, 8, 9], 1, 6⟩,
    ⟨1, 6, [], [], [5], 1, 9⟩,
    ⟨1, 8, [], [], [7], 1, 9⟩,
    ⟨2, 6, [], [], [5], 1, 9⟩,
    ⟨2, 8, [], [], [7], 1, 9⟩,
    ⟨3, 6, [], [], [5], 1, 9⟩,
    ⟨3, 8, [], [], [7], 1, 9⟩,
    ⟨4, 6, [], [], [5], 1, 9⟩,
    ⟨4, 8, [], [], [7], 1, 9⟩,
    ⟨5, 6, [], [], [7], 1, 9⟩,
    ⟨5, 8, [], [], [7], 1, 9⟩,
    ⟨6, 8, [], [5], [7], 1, 8⟩]
  required := []
  closure := []
  bad := ⟨none, {(2, 0), (6, 3), (8, 3), (0, 2), (1, 3)}⟩


private def k11t8p4_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, true, true, true, false, true, false, true],
    #[true, false, true, true, true, true, false, true, false, true],
    #[true, true, false, true, true, true, false, true, false, true],
    #[true, true, true, false, true, true, false, true, false, true],
    #[true, true, true, true, false, true, false, true, false, true],
    #[true, true, true, true, true, false, true, true, false, true],
    #[false, false, false, false, false, true, false, true, false, false],
    #[true, true, true, true, true, true, true, false, true, true],
    #[false, false, false, false, false, false, false, true, false, true],
    #[true, true, true, true, true, true, false, true, true, false]]

private theorem k11t8p4_adjacency_row_0 : ∀ j : Fin 10,
    k11t8p4.graph.Adj 0 j ↔ adjacencyTableLookup k11t8p4_adjacencyTable 0 j.val = true := by decide

private theorem k11t8p4_adjacency_row_1 : ∀ j : Fin 10,
    k11t8p4.graph.Adj 1 j ↔ adjacencyTableLookup k11t8p4_adjacencyTable 1 j.val = true := by decide

private theorem k11t8p4_adjacency_row_2 : ∀ j : Fin 10,
    k11t8p4.graph.Adj 2 j ↔ adjacencyTableLookup k11t8p4_adjacencyTable 2 j.val = true := by decide

private theorem k11t8p4_adjacency_row_3 : ∀ j : Fin 10,
    k11t8p4.graph.Adj 3 j ↔ adjacencyTableLookup k11t8p4_adjacencyTable 3 j.val = true := by decide

private theorem k11t8p4_adjacency_row_4 : ∀ j : Fin 10,
    k11t8p4.graph.Adj 4 j ↔ adjacencyTableLookup k11t8p4_adjacencyTable 4 j.val = true := by decide

private theorem k11t8p4_adjacency_row_5 : ∀ j : Fin 10,
    k11t8p4.graph.Adj 5 j ↔ adjacencyTableLookup k11t8p4_adjacencyTable 5 j.val = true := by decide

private theorem k11t8p4_adjacency_row_6 : ∀ j : Fin 10,
    k11t8p4.graph.Adj 6 j ↔ adjacencyTableLookup k11t8p4_adjacencyTable 6 j.val = true := by decide

private theorem k11t8p4_adjacency_row_7 : ∀ j : Fin 10,
    k11t8p4.graph.Adj 7 j ↔ adjacencyTableLookup k11t8p4_adjacencyTable 7 j.val = true := by decide

private theorem k11t8p4_adjacency_row_8 : ∀ j : Fin 10,
    k11t8p4.graph.Adj 8 j ↔ adjacencyTableLookup k11t8p4_adjacencyTable 8 j.val = true := by decide

private theorem k11t8p4_adjacency_row_9 : ∀ j : Fin 10,
    k11t8p4.graph.Adj 9 j ↔ adjacencyTableLookup k11t8p4_adjacencyTable 9 j.val = true := by decide

private theorem k11t8p4_adjacency_eq : ∀ i j : Fin 10,
    k11t8p4.graph.Adj i j ↔ adjacencyTableLookup k11t8p4_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t8p4_adjacency_row_0 j

  · exact k11t8p4_adjacency_row_1 j

  · exact k11t8p4_adjacency_row_2 j

  · exact k11t8p4_adjacency_row_3 j

  · exact k11t8p4_adjacency_row_4 j

  · exact k11t8p4_adjacency_row_5 j

  · exact k11t8p4_adjacency_row_6 j

  · exact k11t8p4_adjacency_row_7 j

  · exact k11t8p4_adjacency_row_8 j

  · exact k11t8p4_adjacency_row_9 j

private def k11t8p4_tableGraph : SimpleGraph (Fin 10) :=
  adjacencyTableGraph k11t8p4.graph k11t8p4_adjacencyTable k11t8p4_adjacency_eq

private instance k11t8p4_tableGraph_decidableAdj :
    DecidableRel k11t8p4_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t8p4_adjacencyTable i.val j.val = true))

private theorem k11t8p4_tableGraph_eq : k11t8p4_tableGraph = k11t8p4.graph :=
  adjacencyTableGraph_eq k11t8p4.graph k11t8p4_adjacencyTable k11t8p4_adjacency_eq

private def k11t8p4_state_0 : ForbiddenMatrix 10 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 6, Finset.Icc 1 9, ∅, Finset.Icc 1 9, ∅],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 6, Finset.Icc 1 9, ∅, Finset.Icc 1 9, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, ∅, Finset.Icc 1 9, ∅, Finset.Icc 1 9, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, ∅, Finset.Icc 1 9, ∅, Finset.Icc 1 9, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, ∅, Finset.Icc 1 9, ∅, Finset.Icc 1 9, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅, ∅, Finset.Icc 1 9, ∅, Finset.Icc 1 9, ∅],
    #[Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, ∅, ∅, Finset.Icc 1 8, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 8, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t8p4_decode_entry_0 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p4_decode_entry_1 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p4_decode_entry_2 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p4_decode_entry_3 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p4_decode_entry_4 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p4_decode_entry_5 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_6 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_7 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p4_decode_entry_8 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p4_decode_entry_9 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p4_decode_entry_10 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p4_decode_entry_11 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_12 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_13 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_14 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_15 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_16 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_17 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_18 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_19 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_20 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p4_decode_entry_21 : decode 12 510 = Finset.Icc 1 8 := by decide

private def k11t8p4_mask_entries_0 : List (TemplateData (Fin 10) × ℕ) := [(⟨0, 1, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩, 62), (⟨0, 2, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩, 62), (⟨0, 3, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩, 62), (⟨0, 4, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩, 62), (⟨0, 5, [], [], [6, 7, 8, 9], 1, 6⟩, 126), (⟨0, 6, [], [], [5], 1, 9⟩, 1022), (⟨0, 8, [], [], [7], 1, 9⟩, 1022), (⟨1, 2, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩, 62), (⟨1, 3, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩, 62), (⟨1, 4, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩, 62), (⟨1, 5, [], [], [6, 7, 8, 9], 1, 6⟩, 126), (⟨1, 6, [], [], [5], 1, 9⟩, 1022), (⟨1, 8, [], [], [7], 1, 9⟩, 1022), (⟨2, 6, [], [], [5], 1, 9⟩, 1022), (⟨2, 8, [], [], [7], 1, 9⟩, 1022), (⟨3, 6, [], [], [5], 1, 9⟩, 1022), (⟨3, 8, [], [], [7], 1, 9⟩, 1022), (⟨4, 6, [], [], [5], 1, 9⟩, 1022), (⟨4, 8, [], [], [7], 1, 9⟩, 1022), (⟨5, 6, [], [], [7], 1, 9⟩, 1022), (⟨5, 8, [], [], [7], 1, 9⟩, 1022), (⟨6, 8, [], [5], [7], 1, 8⟩, 510)]

private theorem k11t8p4_decode_entries_0 : ∀ Tb ∈ k11t8p4_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t8p4_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p4_decode_entry_0, k11t8p4_decode_entry_1, k11t8p4_decode_entry_2, k11t8p4_decode_entry_3, k11t8p4_decode_entry_4, k11t8p4_decode_entry_5, k11t8p4_decode_entry_6, k11t8p4_decode_entry_7, k11t8p4_decode_entry_8, k11t8p4_decode_entry_9, k11t8p4_decode_entry_10, k11t8p4_decode_entry_11, k11t8p4_decode_entry_12, k11t8p4_decode_entry_13, k11t8p4_decode_entry_14, k11t8p4_decode_entry_15, k11t8p4_decode_entry_16, k11t8p4_decode_entry_17, k11t8p4_decode_entry_18, k11t8p4_decode_entry_19, k11t8p4_decode_entry_20, k11t8p4_decode_entry_21⟩

private def k11t8p4_mask_block_0 : Fin 10 → Fin 10 → ℕ :=
  fun i j => ((#[#[0, 62, 62, 62, 62, 126, 1022, 0, 1022, 0],
    #[62, 0, 62, 62, 62, 126, 1022, 0, 1022, 0],
    #[62, 62, 0, 0, 0, 0, 1022, 0, 1022, 0],
    #[62, 62, 0, 0, 0, 0, 1022, 0, 1022, 0],
    #[62, 62, 0, 0, 0, 0, 1022, 0, 1022, 0],
    #[126, 126, 0, 0, 0, 0, 1022, 0, 1022, 0],
    #[1022, 1022, 1022, 1022, 1022, 1022, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1022, 1022, 1022, 1022, 1022, 1022, 510, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p4_mask_block_0_eq_row_0 : ∀ j : Fin 10, (templateMaskMatrix k11t8p4_mask_entries_0) 0 j = k11t8p4_mask_block_0 0 j := by decide

private theorem k11t8p4_mask_block_0_eq_row_1 : ∀ j : Fin 10, (templateMaskMatrix k11t8p4_mask_entries_0) 1 j = k11t8p4_mask_block_0 1 j := by decide

private theorem k11t8p4_mask_block_0_eq_row_2 : ∀ j : Fin 10, (templateMaskMatrix k11t8p4_mask_entries_0) 2 j = k11t8p4_mask_block_0 2 j := by decide

private theorem k11t8p4_mask_block_0_eq_row_3 : ∀ j : Fin 10, (templateMaskMatrix k11t8p4_mask_entries_0) 3 j = k11t8p4_mask_block_0 3 j := by decide

private theorem k11t8p4_mask_block_0_eq_row_4 : ∀ j : Fin 10, (templateMaskMatrix k11t8p4_mask_entries_0) 4 j = k11t8p4_mask_block_0 4 j := by decide

private theorem k11t8p4_mask_block_0_eq_row_5 : ∀ j : Fin 10, (templateMaskMatrix k11t8p4_mask_entries_0) 5 j = k11t8p4_mask_block_0 5 j := by decide

private theorem k11t8p4_mask_block_0_eq_row_6 : ∀ j : Fin 10, (templateMaskMatrix k11t8p4_mask_entries_0) 6 j = k11t8p4_mask_block_0 6 j := by decide

private theorem k11t8p4_mask_block_0_eq_row_7 : ∀ j : Fin 10, (templateMaskMatrix k11t8p4_mask_entries_0) 7 j = k11t8p4_mask_block_0 7 j := by decide

private theorem k11t8p4_mask_block_0_eq_row_8 : ∀ j : Fin 10, (templateMaskMatrix k11t8p4_mask_entries_0) 8 j = k11t8p4_mask_block_0 8 j := by decide

private theorem k11t8p4_mask_block_0_eq_row_9 : ∀ j : Fin 10, (templateMaskMatrix k11t8p4_mask_entries_0) 9 j = k11t8p4_mask_block_0 9 j := by decide

private theorem k11t8p4_mask_block_0_eq : (templateMaskMatrix k11t8p4_mask_entries_0) = k11t8p4_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t8p4_mask_block_0_eq_row_0 j

  · exact k11t8p4_mask_block_0_eq_row_1 j

  · exact k11t8p4_mask_block_0_eq_row_2 j

  · exact k11t8p4_mask_block_0_eq_row_3 j

  · exact k11t8p4_mask_block_0_eq_row_4 j

  · exact k11t8p4_mask_block_0_eq_row_5 j

  · exact k11t8p4_mask_block_0_eq_row_6 j

  · exact k11t8p4_mask_block_0_eq_row_7 j

  · exact k11t8p4_mask_block_0_eq_row_8 j

  · exact k11t8p4_mask_block_0_eq_row_9 j

private def k11t8p4_mask_entries : List (TemplateData (Fin 10) × ℕ) := k11t8p4_mask_entries_0

private theorem k11t8p4_decode_entries : ∀ Tb ∈ k11t8p4_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t8p4_decode_entries_0

private theorem k11t8p4_mask_entries_map : k11t8p4_mask_entries.map Prod.fst = k11t8p4.templates := by rfl

private def k11t8p4_template_mask : Fin 10 → Fin 10 → ℕ :=
  fun i j => ((#[#[0, 62, 62, 62, 62, 126, 1022, 0, 1022, 0],
    #[62, 0, 62, 62, 62, 126, 1022, 0, 1022, 0],
    #[62, 62, 0, 0, 0, 0, 1022, 0, 1022, 0],
    #[62, 62, 0, 0, 0, 0, 1022, 0, 1022, 0],
    #[62, 62, 0, 0, 0, 0, 1022, 0, 1022, 0],
    #[126, 126, 0, 0, 0, 0, 1022, 0, 1022, 0],
    #[1022, 1022, 1022, 1022, 1022, 1022, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1022, 1022, 1022, 1022, 1022, 1022, 510, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p4_mask_merged_eq_row_0 : ∀ j : Fin 10, (fun i j => k11t8p4_mask_block_0 i j) 0 j = k11t8p4_template_mask 0 j := by decide

private theorem k11t8p4_mask_merged_eq_row_1 : ∀ j : Fin 10, (fun i j => k11t8p4_mask_block_0 i j) 1 j = k11t8p4_template_mask 1 j := by decide

private theorem k11t8p4_mask_merged_eq_row_2 : ∀ j : Fin 10, (fun i j => k11t8p4_mask_block_0 i j) 2 j = k11t8p4_template_mask 2 j := by decide

private theorem k11t8p4_mask_merged_eq_row_3 : ∀ j : Fin 10, (fun i j => k11t8p4_mask_block_0 i j) 3 j = k11t8p4_template_mask 3 j := by decide

private theorem k11t8p4_mask_merged_eq_row_4 : ∀ j : Fin 10, (fun i j => k11t8p4_mask_block_0 i j) 4 j = k11t8p4_template_mask 4 j := by decide

private theorem k11t8p4_mask_merged_eq_row_5 : ∀ j : Fin 10, (fun i j => k11t8p4_mask_block_0 i j) 5 j = k11t8p4_template_mask 5 j := by decide

private theorem k11t8p4_mask_merged_eq_row_6 : ∀ j : Fin 10, (fun i j => k11t8p4_mask_block_0 i j) 6 j = k11t8p4_template_mask 6 j := by decide

private theorem k11t8p4_mask_merged_eq_row_7 : ∀ j : Fin 10, (fun i j => k11t8p4_mask_block_0 i j) 7 j = k11t8p4_template_mask 7 j := by decide

private theorem k11t8p4_mask_merged_eq_row_8 : ∀ j : Fin 10, (fun i j => k11t8p4_mask_block_0 i j) 8 j = k11t8p4_template_mask 8 j := by decide

private theorem k11t8p4_mask_merged_eq_row_9 : ∀ j : Fin 10, (fun i j => k11t8p4_mask_block_0 i j) 9 j = k11t8p4_template_mask 9 j := by decide

private theorem k11t8p4_mask_merged_eq : (fun i j => k11t8p4_mask_block_0 i j) = k11t8p4_template_mask := by
  funext i j
  fin_cases i

  · exact k11t8p4_mask_merged_eq_row_0 j

  · exact k11t8p4_mask_merged_eq_row_1 j

  · exact k11t8p4_mask_merged_eq_row_2 j

  · exact k11t8p4_mask_merged_eq_row_3 j

  · exact k11t8p4_mask_merged_eq_row_4 j

  · exact k11t8p4_mask_merged_eq_row_5 j

  · exact k11t8p4_mask_merged_eq_row_6 j

  · exact k11t8p4_mask_merged_eq_row_7 j

  · exact k11t8p4_mask_merged_eq_row_8 j

  · exact k11t8p4_mask_merged_eq_row_9 j

private theorem k11t8p4_template_mask_eq : templateMaskMatrix k11t8p4_mask_entries = k11t8p4_template_mask := by
  funext i j
  change templateMaskMatrix (k11t8p4_mask_entries_0) i j = _
  simp only [k11t8p4_mask_block_0_eq]
  exact congrFun (congrFun k11t8p4_mask_merged_eq i) j

private theorem k11t8p4_initial_decoded_eq_row_0 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p4_template_mask i j) ∪ requiredMatrix 11 k11t8p4.required i j) 0 j = k11t8p4_state_0 0 j := by decide

private theorem k11t8p4_initial_decoded_eq_row_1 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p4_template_mask i j) ∪ requiredMatrix 11 k11t8p4.required i j) 1 j = k11t8p4_state_0 1 j := by decide

private theorem k11t8p4_initial_decoded_eq_row_2 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p4_template_mask i j) ∪ requiredMatrix 11 k11t8p4.required i j) 2 j = k11t8p4_state_0 2 j := by decide

private theorem k11t8p4_initial_decoded_eq_row_3 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p4_template_mask i j) ∪ requiredMatrix 11 k11t8p4.required i j) 3 j = k11t8p4_state_0 3 j := by decide

private theorem k11t8p4_initial_decoded_eq_row_4 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p4_template_mask i j) ∪ requiredMatrix 11 k11t8p4.required i j) 4 j = k11t8p4_state_0 4 j := by decide

private theorem k11t8p4_initial_decoded_eq_row_5 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p4_template_mask i j) ∪ requiredMatrix 11 k11t8p4.required i j) 5 j = k11t8p4_state_0 5 j := by decide

private theorem k11t8p4_initial_decoded_eq_row_6 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p4_template_mask i j) ∪ requiredMatrix 11 k11t8p4.required i j) 6 j = k11t8p4_state_0 6 j := by decide

private theorem k11t8p4_initial_decoded_eq_row_7 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p4_template_mask i j) ∪ requiredMatrix 11 k11t8p4.required i j) 7 j = k11t8p4_state_0 7 j := by decide

private theorem k11t8p4_initial_decoded_eq_row_8 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p4_template_mask i j) ∪ requiredMatrix 11 k11t8p4.required i j) 8 j = k11t8p4_state_0 8 j := by decide

private theorem k11t8p4_initial_decoded_eq_row_9 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p4_template_mask i j) ∪ requiredMatrix 11 k11t8p4.required i j) 9 j = k11t8p4_state_0 9 j := by decide

private theorem k11t8p4_initial_decoded_eq : (fun i j => decode 12 (k11t8p4_template_mask i j) ∪ requiredMatrix 11 k11t8p4.required i j) = k11t8p4_state_0 := by
  funext i j
  fin_cases i

  · exact k11t8p4_initial_decoded_eq_row_0 j

  · exact k11t8p4_initial_decoded_eq_row_1 j

  · exact k11t8p4_initial_decoded_eq_row_2 j

  · exact k11t8p4_initial_decoded_eq_row_3 j

  · exact k11t8p4_initial_decoded_eq_row_4 j

  · exact k11t8p4_initial_decoded_eq_row_5 j

  · exact k11t8p4_initial_decoded_eq_row_6 j

  · exact k11t8p4_initial_decoded_eq_row_7 j

  · exact k11t8p4_initial_decoded_eq_row_8 j

  · exact k11t8p4_initial_decoded_eq_row_9 j

private theorem k11t8p4_initial_eq : k11t8p4.initialMatrix 11 = k11t8p4_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t8p4_mask_entries k11t8p4_decode_entries
  rw [k11t8p4_mask_entries_map, k11t8p4_template_mask_eq] at h
  funext i j
  change templateMatrix k11t8p4.templates i j ∪ requiredMatrix 11 k11t8p4.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t8p4_initial_decoded_eq i) j

private theorem k11t8p4_closure_0 : ClosureCheck k11t8p4.graph k11t8p4_state_0 11 8 [] := by trivial

private theorem k11t8p4_matrix_eq : k11t8p4.matrix 11 = k11t8p4_state_0 := by
  change closureMatrix (k11t8p4.initialMatrix 11) _ = _
  rw [k11t8p4_initial_eq]
  change closureMatrix k11t8p4_state_0 [] = _
  rfl

private theorem k11t8p4_part_0 : k11t8p4.chains.flatten = List.finRange _ := by decide

private theorem k11t8p4_part_1 : k11t8p4.chains.map List.length = ([[], [], [], [], [], [1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t8p4_part_2 : k11t8p4.chains.map (fun l => l.map (fun i => decide (i ∈ k11t8p4.clique))) = ([[], [], [], [], [], [1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k11t8p4_templates_item_0 : (⟨0, 1, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_1 : (⟨0, 2, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_2 : (⟨0, 3, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_3 : (⟨0, 4, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_4 : (⟨0, 5, [], [], [6, 7, 8, 9], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_5 : (⟨0, 6, [], [], [5], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_6 : (⟨0, 8, [], [], [7], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_7 : (⟨1, 2, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_8 : (⟨1, 3, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_9 : (⟨1, 4, [[5, 6, 7, 8, 9]], [], [], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_10 : (⟨1, 5, [], [], [6, 7, 8, 9], 1, 6⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_11 : (⟨1, 6, [], [], [5], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_12 : (⟨1, 8, [], [], [7], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_13 : (⟨2, 6, [], [], [5], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_14 : (⟨2, 8, [], [], [7], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_15 : (⟨3, 6, [], [], [5], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_16 : (⟨3, 8, [], [], [7], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_17 : (⟨4, 6, [], [], [5], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_18 : (⟨4, 8, [], [], [7], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_19 : (⟨5, 6, [], [], [7], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_20 : (⟨5, 8, [], [], [7], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_item_21 : (⟨6, 8, [], [5], [7], 1, 8⟩ : TemplateData (Fin 10)).Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p4_tableGraph_eq]
  decide

private theorem k11t8p4_templates_fast_block_0_check : ∀ T ∈ k11t8p4_mask_entries_0.map Prod.fst, T.Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t8p4_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p4_templates_item_0, k11t8p4_templates_item_1, k11t8p4_templates_item_2, k11t8p4_templates_item_3, k11t8p4_templates_item_4, k11t8p4_templates_item_5, k11t8p4_templates_item_6, k11t8p4_templates_item_7, k11t8p4_templates_item_8, k11t8p4_templates_item_9, k11t8p4_templates_item_10, k11t8p4_templates_item_11, k11t8p4_templates_item_12, k11t8p4_templates_item_13, k11t8p4_templates_item_14, k11t8p4_templates_item_15, k11t8p4_templates_item_16, k11t8p4_templates_item_17, k11t8p4_templates_item_18, k11t8p4_templates_item_19, k11t8p4_templates_item_20, k11t8p4_templates_item_21⟩

private theorem k11t8p4_part_3 : ∀ T ∈ k11t8p4.templates, T.Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t8p4_mask_entries_0.map Prod.fst), T.Check k11t8p4.graph k11t8p4.clique 11 (patternAmount ([[], [], [], [], [], [1, 1]] : List (List ℕ))) (([[], [], [], [], [], [1, 1]] : List (List ℕ)).map List.length).sum
  exact k11t8p4_templates_fast_block_0_check

private theorem k11t8p4_part_4 : ∀ p ∈ k11t8p4.required, p.Check k11t8p4.graph 11 := by decide

private theorem k11t8p4_part_5 : ClosureCheck k11t8p4.graph (k11t8p4.initialMatrix 11) 11 8 k11t8p4.closure := by
  rw [k11t8p4_initial_eq]
  exact k11t8p4_closure_0

private theorem k11t8p4_part_6 : k11t8p4.bad.Check k11t8p4.graph (k11t8p4.matrix 11) 11 8 := by
  rw [k11t8p4_matrix_eq]
  decide

theorem k11t8p4_check : k11t8p4.Check 11 8 [[], [], [], [], [], [1, 1]] :=
  ⟨k11t8p4_part_0, k11t8p4_part_1, k11t8p4_part_2, k11t8p4_part_3, k11t8p4_part_4, k11t8p4_part_5, k11t8p4_part_6⟩
def k11t8p5 : LayoutCertificate 11 where
  chains := [[0], [1], [2], [3], [4], [5, 6, 7, 8, 9, 10]]
  clique := {0, 1, 2, 3, 4, 5, 7, 10}
  templates := [⟨0, 1, [], [], [], 3, 10⟩,
    ⟨0, 1, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩,
    ⟨0, 2, [], [], [], 3, 10⟩,
    ⟨0, 2, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩,
    ⟨0, 3, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩,
    ⟨0, 4, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩,
    ⟨0, 5, [], [], [6, 7, 8, 9, 10], 1, 5⟩,
    ⟨0, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩,
    ⟨0, 8, [], [], [9, 10], 1, 8⟩,
    ⟨0, 9, [], [], [8, 7], 1, 8⟩,
    ⟨1, 2, [], [], [], 3, 10⟩,
    ⟨1, 2, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩,
    ⟨1, 3, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩,
    ⟨1, 4, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩,
    ⟨1, 5, [], [], [6, 7, 8, 9, 10], 1, 5⟩,
    ⟨1, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩,
    ⟨1, 8, [], [], [9, 10], 1, 8⟩,
    ⟨1, 9, [], [], [8, 7], 1, 8⟩,
    ⟨2, 3, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩,
    ⟨2, 4, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩,
    ⟨2, 5, [], [], [6, 7, 8, 9, 10], 1, 5⟩,
    ⟨2, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩,
    ⟨2, 8, [], [], [9, 10], 1, 8⟩,
    ⟨2, 9, [], [], [8, 7], 1, 8⟩,
    ⟨3, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩,
    ⟨4, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩,
    ⟨5, 6, [], [], [7, 8, 9, 10], 1, 6⟩,
    ⟨6, 7, [], [5], [8, 9, 10], 1, 6⟩,
    ⟨6, 8, [], [5], [7], 1, 8⟩]
  required := []
  closure := []
  bad := ⟨none, {(8, 0), (6, 2), (0, 3), (1, 3), (2, 3)}⟩


private def k11t8p5_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, true, true, true, false, true, false, false, true],
    #[true, false, true, true, true, true, false, true, false, false, true],
    #[true, true, false, true, true, true, false, true, false, false, true],
    #[true, true, true, false, true, true, false, true, false, false, true],
    #[true, true, true, true, false, true, false, true, false, false, true],
    #[true, true, true, true, true, false, true, true, false, false, true],
    #[false, false, false, false, false, true, false, true, false, false, false],
    #[true, true, true, true, true, true, true, false, true, false, true],
    #[false, false, false, false, false, false, false, true, false, true, false],
    #[false, false, false, false, false, false, false, false, true, false, true],
    #[true, true, true, true, true, true, false, true, false, true, false]]

private theorem k11t8p5_adjacency_row_0 : ∀ j : Fin 11,
    k11t8p5.graph.Adj 0 j ↔ adjacencyTableLookup k11t8p5_adjacencyTable 0 j.val = true := by decide

private theorem k11t8p5_adjacency_row_1 : ∀ j : Fin 11,
    k11t8p5.graph.Adj 1 j ↔ adjacencyTableLookup k11t8p5_adjacencyTable 1 j.val = true := by decide

private theorem k11t8p5_adjacency_row_2 : ∀ j : Fin 11,
    k11t8p5.graph.Adj 2 j ↔ adjacencyTableLookup k11t8p5_adjacencyTable 2 j.val = true := by decide

private theorem k11t8p5_adjacency_row_3 : ∀ j : Fin 11,
    k11t8p5.graph.Adj 3 j ↔ adjacencyTableLookup k11t8p5_adjacencyTable 3 j.val = true := by decide

private theorem k11t8p5_adjacency_row_4 : ∀ j : Fin 11,
    k11t8p5.graph.Adj 4 j ↔ adjacencyTableLookup k11t8p5_adjacencyTable 4 j.val = true := by decide

private theorem k11t8p5_adjacency_row_5 : ∀ j : Fin 11,
    k11t8p5.graph.Adj 5 j ↔ adjacencyTableLookup k11t8p5_adjacencyTable 5 j.val = true := by decide

private theorem k11t8p5_adjacency_row_6 : ∀ j : Fin 11,
    k11t8p5.graph.Adj 6 j ↔ adjacencyTableLookup k11t8p5_adjacencyTable 6 j.val = true := by decide

private theorem k11t8p5_adjacency_row_7 : ∀ j : Fin 11,
    k11t8p5.graph.Adj 7 j ↔ adjacencyTableLookup k11t8p5_adjacencyTable 7 j.val = true := by decide

private theorem k11t8p5_adjacency_row_8 : ∀ j : Fin 11,
    k11t8p5.graph.Adj 8 j ↔ adjacencyTableLookup k11t8p5_adjacencyTable 8 j.val = true := by decide

private theorem k11t8p5_adjacency_row_9 : ∀ j : Fin 11,
    k11t8p5.graph.Adj 9 j ↔ adjacencyTableLookup k11t8p5_adjacencyTable 9 j.val = true := by decide

private theorem k11t8p5_adjacency_row_10 : ∀ j : Fin 11,
    k11t8p5.graph.Adj 10 j ↔ adjacencyTableLookup k11t8p5_adjacencyTable 10 j.val = true := by decide

private theorem k11t8p5_adjacency_eq : ∀ i j : Fin 11,
    k11t8p5.graph.Adj i j ↔ adjacencyTableLookup k11t8p5_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t8p5_adjacency_row_0 j

  · exact k11t8p5_adjacency_row_1 j

  · exact k11t8p5_adjacency_row_2 j

  · exact k11t8p5_adjacency_row_3 j

  · exact k11t8p5_adjacency_row_4 j

  · exact k11t8p5_adjacency_row_5 j

  · exact k11t8p5_adjacency_row_6 j

  · exact k11t8p5_adjacency_row_7 j

  · exact k11t8p5_adjacency_row_8 j

  · exact k11t8p5_adjacency_row_9 j

  · exact k11t8p5_adjacency_row_10 j

private def k11t8p5_tableGraph : SimpleGraph (Fin 11) :=
  adjacencyTableGraph k11t8p5.graph k11t8p5_adjacencyTable k11t8p5_adjacency_eq

private instance k11t8p5_tableGraph_decidableAdj :
    DecidableRel k11t8p5_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t8p5_adjacencyTable i.val j.val = true))

private theorem k11t8p5_tableGraph_eq : k11t8p5_tableGraph = k11t8p5.graph :=
  adjacencyTableGraph_eq k11t8p5.graph k11t8p5_adjacencyTable k11t8p5_adjacency_eq

private def k11t8p5_state_0 : ForbiddenMatrix 11 :=
  fun i j => ((#[#[∅, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 8, Finset.Icc 1 8, ∅],
    #[Finset.Icc 1 10, ∅, Finset.Icc 1 10, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 8, Finset.Icc 1 8, ∅],
    #[Finset.Icc 1 10, Finset.Icc 1 10, ∅, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 8, Finset.Icc 1 8, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅, ∅, ∅, Finset.Icc 1 5, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅, ∅, ∅, Finset.Icc 1 5, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, Finset.Icc 1 6, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 8, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, Finset.Icc 1 6, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 8, Finset.Icc 1 8, Finset.Icc 1 8, ∅, ∅, ∅, Finset.Icc 1 8, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 8, Finset.Icc 1 8, Finset.Icc 1 8, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t8p5_decode_entry_0 : decode 12 2040 = Finset.Icc 3 10 := by decide

private theorem k11t8p5_decode_entry_1 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p5_decode_entry_2 : decode 12 2040 = Finset.Icc 3 10 := by decide

private theorem k11t8p5_decode_entry_3 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p5_decode_entry_4 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p5_decode_entry_5 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p5_decode_entry_6 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p5_decode_entry_7 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p5_decode_entry_8 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p5_decode_entry_9 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p5_decode_entry_10 : decode 12 2040 = Finset.Icc 3 10 := by decide

private theorem k11t8p5_decode_entry_11 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p5_decode_entry_12 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p5_decode_entry_13 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p5_decode_entry_14 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p5_decode_entry_15 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p5_decode_entry_16 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p5_decode_entry_17 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p5_decode_entry_18 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p5_decode_entry_19 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p5_decode_entry_20 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p5_decode_entry_21 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p5_decode_entry_22 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p5_decode_entry_23 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p5_decode_entry_24 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p5_decode_entry_25 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p5_decode_entry_26 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p5_decode_entry_27 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p5_decode_entry_28 : decode 12 510 = Finset.Icc 1 8 := by decide

private def k11t8p5_mask_entries_0 : List (TemplateData (Fin 11) × ℕ) := [(⟨0, 1, [], [], [], 3, 10⟩, 2040), (⟨0, 1, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩, 30), (⟨0, 2, [], [], [], 3, 10⟩, 2040), (⟨0, 2, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩, 30), (⟨0, 3, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩, 30), (⟨0, 4, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩, 30), (⟨0, 5, [], [], [6, 7, 8, 9, 10], 1, 5⟩, 62), (⟨0, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩, 62), (⟨0, 8, [], [], [9, 10], 1, 8⟩, 510), (⟨0, 9, [], [], [8, 7], 1, 8⟩, 510), (⟨1, 2, [], [], [], 3, 10⟩, 2040), (⟨1, 2, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩, 30), (⟨1, 3, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩, 30), (⟨1, 4, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩, 30), (⟨1, 5, [], [], [6, 7, 8, 9, 10], 1, 5⟩, 62), (⟨1, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩, 62), (⟨1, 8, [], [], [9, 10], 1, 8⟩, 510), (⟨1, 9, [], [], [8, 7], 1, 8⟩, 510), (⟨2, 3, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩, 30), (⟨2, 4, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩, 30), (⟨2, 5, [], [], [6, 7, 8, 9, 10], 1, 5⟩, 62), (⟨2, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩, 62), (⟨2, 8, [], [], [9, 10], 1, 8⟩, 510), (⟨2, 9, [], [], [8, 7], 1, 8⟩, 510), (⟨3, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩, 62), (⟨4, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩, 62), (⟨5, 6, [], [], [7, 8, 9, 10], 1, 6⟩, 126), (⟨6, 7, [], [5], [8, 9, 10], 1, 6⟩, 126), (⟨6, 8, [], [5], [7], 1, 8⟩, 510)]

private theorem k11t8p5_decode_entries_0 : ∀ Tb ∈ k11t8p5_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t8p5_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p5_decode_entry_0, k11t8p5_decode_entry_1, k11t8p5_decode_entry_2, k11t8p5_decode_entry_3, k11t8p5_decode_entry_4, k11t8p5_decode_entry_5, k11t8p5_decode_entry_6, k11t8p5_decode_entry_7, k11t8p5_decode_entry_8, k11t8p5_decode_entry_9, k11t8p5_decode_entry_10, k11t8p5_decode_entry_11, k11t8p5_decode_entry_12, k11t8p5_decode_entry_13, k11t8p5_decode_entry_14, k11t8p5_decode_entry_15, k11t8p5_decode_entry_16, k11t8p5_decode_entry_17, k11t8p5_decode_entry_18, k11t8p5_decode_entry_19, k11t8p5_decode_entry_20, k11t8p5_decode_entry_21, k11t8p5_decode_entry_22, k11t8p5_decode_entry_23, k11t8p5_decode_entry_24, k11t8p5_decode_entry_25, k11t8p5_decode_entry_26, k11t8p5_decode_entry_27, k11t8p5_decode_entry_28⟩

private def k11t8p5_mask_block_0 : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 2046, 2046, 30, 30, 62, 62, 0, 510, 510, 0],
    #[2046, 0, 2046, 30, 30, 62, 62, 0, 510, 510, 0],
    #[2046, 2046, 0, 30, 30, 62, 62, 0, 510, 510, 0],
    #[30, 30, 30, 0, 0, 0, 62, 0, 0, 0, 0],
    #[30, 30, 30, 0, 0, 0, 62, 0, 0, 0, 0],
    #[62, 62, 62, 0, 0, 0, 126, 0, 0, 0, 0],
    #[62, 62, 62, 62, 62, 126, 0, 126, 510, 0, 0],
    #[0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0],
    #[510, 510, 510, 0, 0, 0, 510, 0, 0, 0, 0],
    #[510, 510, 510, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p5_mask_block_0_eq_row_0 : ∀ j : Fin 11, (templateMaskMatrix k11t8p5_mask_entries_0) 0 j = k11t8p5_mask_block_0 0 j := by decide

private theorem k11t8p5_mask_block_0_eq_row_1 : ∀ j : Fin 11, (templateMaskMatrix k11t8p5_mask_entries_0) 1 j = k11t8p5_mask_block_0 1 j := by decide

private theorem k11t8p5_mask_block_0_eq_row_2 : ∀ j : Fin 11, (templateMaskMatrix k11t8p5_mask_entries_0) 2 j = k11t8p5_mask_block_0 2 j := by decide

private theorem k11t8p5_mask_block_0_eq_row_3 : ∀ j : Fin 11, (templateMaskMatrix k11t8p5_mask_entries_0) 3 j = k11t8p5_mask_block_0 3 j := by decide

private theorem k11t8p5_mask_block_0_eq_row_4 : ∀ j : Fin 11, (templateMaskMatrix k11t8p5_mask_entries_0) 4 j = k11t8p5_mask_block_0 4 j := by decide

private theorem k11t8p5_mask_block_0_eq_row_5 : ∀ j : Fin 11, (templateMaskMatrix k11t8p5_mask_entries_0) 5 j = k11t8p5_mask_block_0 5 j := by decide

private theorem k11t8p5_mask_block_0_eq_row_6 : ∀ j : Fin 11, (templateMaskMatrix k11t8p5_mask_entries_0) 6 j = k11t8p5_mask_block_0 6 j := by decide

private theorem k11t8p5_mask_block_0_eq_row_7 : ∀ j : Fin 11, (templateMaskMatrix k11t8p5_mask_entries_0) 7 j = k11t8p5_mask_block_0 7 j := by decide

private theorem k11t8p5_mask_block_0_eq_row_8 : ∀ j : Fin 11, (templateMaskMatrix k11t8p5_mask_entries_0) 8 j = k11t8p5_mask_block_0 8 j := by decide

private theorem k11t8p5_mask_block_0_eq_row_9 : ∀ j : Fin 11, (templateMaskMatrix k11t8p5_mask_entries_0) 9 j = k11t8p5_mask_block_0 9 j := by decide

private theorem k11t8p5_mask_block_0_eq_row_10 : ∀ j : Fin 11, (templateMaskMatrix k11t8p5_mask_entries_0) 10 j = k11t8p5_mask_block_0 10 j := by decide

private theorem k11t8p5_mask_block_0_eq : (templateMaskMatrix k11t8p5_mask_entries_0) = k11t8p5_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t8p5_mask_block_0_eq_row_0 j

  · exact k11t8p5_mask_block_0_eq_row_1 j

  · exact k11t8p5_mask_block_0_eq_row_2 j

  · exact k11t8p5_mask_block_0_eq_row_3 j

  · exact k11t8p5_mask_block_0_eq_row_4 j

  · exact k11t8p5_mask_block_0_eq_row_5 j

  · exact k11t8p5_mask_block_0_eq_row_6 j

  · exact k11t8p5_mask_block_0_eq_row_7 j

  · exact k11t8p5_mask_block_0_eq_row_8 j

  · exact k11t8p5_mask_block_0_eq_row_9 j

  · exact k11t8p5_mask_block_0_eq_row_10 j

private def k11t8p5_mask_entries : List (TemplateData (Fin 11) × ℕ) := k11t8p5_mask_entries_0

private theorem k11t8p5_decode_entries : ∀ Tb ∈ k11t8p5_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t8p5_decode_entries_0

private theorem k11t8p5_mask_entries_map : k11t8p5_mask_entries.map Prod.fst = k11t8p5.templates := by rfl

private def k11t8p5_template_mask : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 2046, 2046, 30, 30, 62, 62, 0, 510, 510, 0],
    #[2046, 0, 2046, 30, 30, 62, 62, 0, 510, 510, 0],
    #[2046, 2046, 0, 30, 30, 62, 62, 0, 510, 510, 0],
    #[30, 30, 30, 0, 0, 0, 62, 0, 0, 0, 0],
    #[30, 30, 30, 0, 0, 0, 62, 0, 0, 0, 0],
    #[62, 62, 62, 0, 0, 0, 126, 0, 0, 0, 0],
    #[62, 62, 62, 62, 62, 126, 0, 126, 510, 0, 0],
    #[0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0],
    #[510, 510, 510, 0, 0, 0, 510, 0, 0, 0, 0],
    #[510, 510, 510, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p5_mask_merged_eq_row_0 : ∀ j : Fin 11, (fun i j => k11t8p5_mask_block_0 i j) 0 j = k11t8p5_template_mask 0 j := by decide

private theorem k11t8p5_mask_merged_eq_row_1 : ∀ j : Fin 11, (fun i j => k11t8p5_mask_block_0 i j) 1 j = k11t8p5_template_mask 1 j := by decide

private theorem k11t8p5_mask_merged_eq_row_2 : ∀ j : Fin 11, (fun i j => k11t8p5_mask_block_0 i j) 2 j = k11t8p5_template_mask 2 j := by decide

private theorem k11t8p5_mask_merged_eq_row_3 : ∀ j : Fin 11, (fun i j => k11t8p5_mask_block_0 i j) 3 j = k11t8p5_template_mask 3 j := by decide

private theorem k11t8p5_mask_merged_eq_row_4 : ∀ j : Fin 11, (fun i j => k11t8p5_mask_block_0 i j) 4 j = k11t8p5_template_mask 4 j := by decide

private theorem k11t8p5_mask_merged_eq_row_5 : ∀ j : Fin 11, (fun i j => k11t8p5_mask_block_0 i j) 5 j = k11t8p5_template_mask 5 j := by decide

private theorem k11t8p5_mask_merged_eq_row_6 : ∀ j : Fin 11, (fun i j => k11t8p5_mask_block_0 i j) 6 j = k11t8p5_template_mask 6 j := by decide

private theorem k11t8p5_mask_merged_eq_row_7 : ∀ j : Fin 11, (fun i j => k11t8p5_mask_block_0 i j) 7 j = k11t8p5_template_mask 7 j := by decide

private theorem k11t8p5_mask_merged_eq_row_8 : ∀ j : Fin 11, (fun i j => k11t8p5_mask_block_0 i j) 8 j = k11t8p5_template_mask 8 j := by decide

private theorem k11t8p5_mask_merged_eq_row_9 : ∀ j : Fin 11, (fun i j => k11t8p5_mask_block_0 i j) 9 j = k11t8p5_template_mask 9 j := by decide

private theorem k11t8p5_mask_merged_eq_row_10 : ∀ j : Fin 11, (fun i j => k11t8p5_mask_block_0 i j) 10 j = k11t8p5_template_mask 10 j := by decide

private theorem k11t8p5_mask_merged_eq : (fun i j => k11t8p5_mask_block_0 i j) = k11t8p5_template_mask := by
  funext i j
  fin_cases i

  · exact k11t8p5_mask_merged_eq_row_0 j

  · exact k11t8p5_mask_merged_eq_row_1 j

  · exact k11t8p5_mask_merged_eq_row_2 j

  · exact k11t8p5_mask_merged_eq_row_3 j

  · exact k11t8p5_mask_merged_eq_row_4 j

  · exact k11t8p5_mask_merged_eq_row_5 j

  · exact k11t8p5_mask_merged_eq_row_6 j

  · exact k11t8p5_mask_merged_eq_row_7 j

  · exact k11t8p5_mask_merged_eq_row_8 j

  · exact k11t8p5_mask_merged_eq_row_9 j

  · exact k11t8p5_mask_merged_eq_row_10 j

private theorem k11t8p5_template_mask_eq : templateMaskMatrix k11t8p5_mask_entries = k11t8p5_template_mask := by
  funext i j
  change templateMaskMatrix (k11t8p5_mask_entries_0) i j = _
  simp only [k11t8p5_mask_block_0_eq]
  exact congrFun (congrFun k11t8p5_mask_merged_eq i) j

private theorem k11t8p5_initial_decoded_eq_row_0 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) 0 j = k11t8p5_state_0 0 j := by decide

private theorem k11t8p5_initial_decoded_eq_row_1 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) 1 j = k11t8p5_state_0 1 j := by decide

private theorem k11t8p5_initial_decoded_eq_row_2 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) 2 j = k11t8p5_state_0 2 j := by decide

private theorem k11t8p5_initial_decoded_eq_row_3 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) 3 j = k11t8p5_state_0 3 j := by decide

private theorem k11t8p5_initial_decoded_eq_row_4 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) 4 j = k11t8p5_state_0 4 j := by decide

private theorem k11t8p5_initial_decoded_eq_row_5 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) 5 j = k11t8p5_state_0 5 j := by decide

private theorem k11t8p5_initial_decoded_eq_row_6 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) 6 j = k11t8p5_state_0 6 j := by decide

private theorem k11t8p5_initial_decoded_eq_row_7 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) 7 j = k11t8p5_state_0 7 j := by decide

private theorem k11t8p5_initial_decoded_eq_row_8 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) 8 j = k11t8p5_state_0 8 j := by decide

private theorem k11t8p5_initial_decoded_eq_row_9 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) 9 j = k11t8p5_state_0 9 j := by decide

private theorem k11t8p5_initial_decoded_eq_row_10 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) 10 j = k11t8p5_state_0 10 j := by decide

private theorem k11t8p5_initial_decoded_eq : (fun i j => decode 12 (k11t8p5_template_mask i j) ∪ requiredMatrix 11 k11t8p5.required i j) = k11t8p5_state_0 := by
  funext i j
  fin_cases i

  · exact k11t8p5_initial_decoded_eq_row_0 j

  · exact k11t8p5_initial_decoded_eq_row_1 j

  · exact k11t8p5_initial_decoded_eq_row_2 j

  · exact k11t8p5_initial_decoded_eq_row_3 j

  · exact k11t8p5_initial_decoded_eq_row_4 j

  · exact k11t8p5_initial_decoded_eq_row_5 j

  · exact k11t8p5_initial_decoded_eq_row_6 j

  · exact k11t8p5_initial_decoded_eq_row_7 j

  · exact k11t8p5_initial_decoded_eq_row_8 j

  · exact k11t8p5_initial_decoded_eq_row_9 j

  · exact k11t8p5_initial_decoded_eq_row_10 j

private theorem k11t8p5_initial_eq : k11t8p5.initialMatrix 11 = k11t8p5_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t8p5_mask_entries k11t8p5_decode_entries
  rw [k11t8p5_mask_entries_map, k11t8p5_template_mask_eq] at h
  funext i j
  change templateMatrix k11t8p5.templates i j ∪ requiredMatrix 11 k11t8p5.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t8p5_initial_decoded_eq i) j

private theorem k11t8p5_closure_0 : ClosureCheck k11t8p5.graph k11t8p5_state_0 11 8 [] := by trivial

private theorem k11t8p5_matrix_eq : k11t8p5.matrix 11 = k11t8p5_state_0 := by
  change closureMatrix (k11t8p5.initialMatrix 11) _ = _
  rw [k11t8p5_initial_eq]
  change closureMatrix k11t8p5_state_0 [] = _
  rfl

private theorem k11t8p5_part_0 : k11t8p5.chains.flatten = List.finRange _ := by decide

private theorem k11t8p5_part_1 : k11t8p5.chains.map List.length = ([[], [], [], [], [], [1, 2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t8p5_part_2 : k11t8p5.chains.map (fun l => l.map (fun i => decide (i ∈ k11t8p5.clique))) = ([[], [], [], [], [], [1, 2]] : List (List ℕ)).map profileMask := by decide

private theorem k11t8p5_templates_item_0 : (⟨0, 1, [], [], [], 3, 10⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_1 : (⟨0, 1, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_2 : (⟨0, 2, [], [], [], 3, 10⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_3 : (⟨0, 2, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_4 : (⟨0, 3, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_5 : (⟨0, 4, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_6 : (⟨0, 5, [], [], [6, 7, 8, 9, 10], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_7 : (⟨0, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_8 : (⟨0, 8, [], [], [9, 10], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_9 : (⟨0, 9, [], [], [8, 7], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_10 : (⟨1, 2, [], [], [], 3, 10⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_11 : (⟨1, 2, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_12 : (⟨1, 3, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_13 : (⟨1, 4, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_14 : (⟨1, 5, [], [], [6, 7, 8, 9, 10], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_15 : (⟨1, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_16 : (⟨1, 8, [], [], [9, 10], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_17 : (⟨1, 9, [], [], [8, 7], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_18 : (⟨2, 3, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_19 : (⟨2, 4, [[5, 6, 7, 8, 9, 10]], [], [], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_20 : (⟨2, 5, [], [], [6, 7, 8, 9, 10], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_21 : (⟨2, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_22 : (⟨2, 8, [], [], [9, 10], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_23 : (⟨2, 9, [], [], [8, 7], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_24 : (⟨3, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_25 : (⟨4, 6, [[7, 8, 9, 10]], [], [5], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_26 : (⟨5, 6, [], [], [7, 8, 9, 10], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_27 : (⟨6, 7, [], [5], [8, 9, 10], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_item_28 : (⟨6, 8, [], [5], [7], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p5_tableGraph_eq]
  decide

private theorem k11t8p5_templates_fast_block_0_check : ∀ T ∈ k11t8p5_mask_entries_0.map Prod.fst, T.Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t8p5_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p5_templates_item_0, k11t8p5_templates_item_1, k11t8p5_templates_item_2, k11t8p5_templates_item_3, k11t8p5_templates_item_4, k11t8p5_templates_item_5, k11t8p5_templates_item_6, k11t8p5_templates_item_7, k11t8p5_templates_item_8, k11t8p5_templates_item_9, k11t8p5_templates_item_10, k11t8p5_templates_item_11, k11t8p5_templates_item_12, k11t8p5_templates_item_13, k11t8p5_templates_item_14, k11t8p5_templates_item_15, k11t8p5_templates_item_16, k11t8p5_templates_item_17, k11t8p5_templates_item_18, k11t8p5_templates_item_19, k11t8p5_templates_item_20, k11t8p5_templates_item_21, k11t8p5_templates_item_22, k11t8p5_templates_item_23, k11t8p5_templates_item_24, k11t8p5_templates_item_25, k11t8p5_templates_item_26, k11t8p5_templates_item_27, k11t8p5_templates_item_28⟩

private theorem k11t8p5_part_3 : ∀ T ∈ k11t8p5.templates, T.Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t8p5_mask_entries_0.map Prod.fst), T.Check k11t8p5.graph k11t8p5.clique 11 (patternAmount ([[], [], [], [], [], [1, 2]] : List (List ℕ))) (([[], [], [], [], [], [1, 2]] : List (List ℕ)).map List.length).sum
  exact k11t8p5_templates_fast_block_0_check

private theorem k11t8p5_part_4 : ∀ p ∈ k11t8p5.required, p.Check k11t8p5.graph 11 := by decide

private theorem k11t8p5_part_5 : ClosureCheck k11t8p5.graph (k11t8p5.initialMatrix 11) 11 8 k11t8p5.closure := by
  rw [k11t8p5_initial_eq]
  exact k11t8p5_closure_0

private theorem k11t8p5_part_6 : k11t8p5.bad.Check k11t8p5.graph (k11t8p5.matrix 11) 11 8 := by
  rw [k11t8p5_matrix_eq]
  decide

theorem k11t8p5_check : k11t8p5.Check 11 8 [[], [], [], [], [], [1, 2]] :=
  ⟨k11t8p5_part_0, k11t8p5_part_1, k11t8p5_part_2, k11t8p5_part_3, k11t8p5_part_4, k11t8p5_part_5, k11t8p5_part_6⟩
def k11t8p6 : LayoutCertificate 10 where
  chains := [[0], [1], [2], [3], [4, 5, 6], [7, 8, 9]]
  clique := {0, 1, 2, 3, 4, 6, 7, 9}
  templates := [⟨0, 1, [], [], [], 2, 10⟩,
    ⟨0, 1, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩,
    ⟨0, 2, [], [], [], 2, 10⟩,
    ⟨0, 2, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩,
    ⟨0, 3, [], [], [], 2, 10⟩,
    ⟨0, 3, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩,
    ⟨0, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩,
    ⟨0, 5, [], [], [4], 1, 9⟩,
    ⟨0, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩,
    ⟨0, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩,
    ⟨1, 2, [], [], [], 2, 10⟩,
    ⟨1, 2, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩,
    ⟨1, 3, [], [], [], 2, 10⟩,
    ⟨1, 3, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩,
    ⟨1, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩,
    ⟨1, 5, [], [], [4], 1, 9⟩,
    ⟨1, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩,
    ⟨1, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩,
    ⟨2, 3, [], [], [], 2, 10⟩,
    ⟨2, 3, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩,
    ⟨2, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩,
    ⟨2, 5, [], [], [4], 1, 9⟩,
    ⟨2, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩,
    ⟨2, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩,
    ⟨3, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩,
    ⟨3, 5, [], [], [4], 1, 9⟩,
    ⟨3, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩,
    ⟨3, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(5, 0), (0, 2), (1, 3), (2, 3), (3, 3)}⟩


private def k11t8p6_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, true, true, false, true, true, false, true],
    #[true, false, true, true, true, false, true, true, false, true],
    #[true, true, false, true, true, false, true, true, false, true],
    #[true, true, true, false, true, false, true, true, false, true],
    #[true, true, true, true, false, true, true, true, false, true],
    #[false, false, false, false, true, false, true, false, false, false],
    #[true, true, true, true, true, true, false, true, false, true],
    #[true, true, true, true, true, false, true, false, true, true],
    #[false, false, false, false, false, false, false, true, false, true],
    #[true, true, true, true, true, false, true, true, true, false]]

private theorem k11t8p6_adjacency_row_0 : ∀ j : Fin 10,
    k11t8p6.graph.Adj 0 j ↔ adjacencyTableLookup k11t8p6_adjacencyTable 0 j.val = true := by decide

private theorem k11t8p6_adjacency_row_1 : ∀ j : Fin 10,
    k11t8p6.graph.Adj 1 j ↔ adjacencyTableLookup k11t8p6_adjacencyTable 1 j.val = true := by decide

private theorem k11t8p6_adjacency_row_2 : ∀ j : Fin 10,
    k11t8p6.graph.Adj 2 j ↔ adjacencyTableLookup k11t8p6_adjacencyTable 2 j.val = true := by decide

private theorem k11t8p6_adjacency_row_3 : ∀ j : Fin 10,
    k11t8p6.graph.Adj 3 j ↔ adjacencyTableLookup k11t8p6_adjacencyTable 3 j.val = true := by decide

private theorem k11t8p6_adjacency_row_4 : ∀ j : Fin 10,
    k11t8p6.graph.Adj 4 j ↔ adjacencyTableLookup k11t8p6_adjacencyTable 4 j.val = true := by decide

private theorem k11t8p6_adjacency_row_5 : ∀ j : Fin 10,
    k11t8p6.graph.Adj 5 j ↔ adjacencyTableLookup k11t8p6_adjacencyTable 5 j.val = true := by decide

private theorem k11t8p6_adjacency_row_6 : ∀ j : Fin 10,
    k11t8p6.graph.Adj 6 j ↔ adjacencyTableLookup k11t8p6_adjacencyTable 6 j.val = true := by decide

private theorem k11t8p6_adjacency_row_7 : ∀ j : Fin 10,
    k11t8p6.graph.Adj 7 j ↔ adjacencyTableLookup k11t8p6_adjacencyTable 7 j.val = true := by decide

private theorem k11t8p6_adjacency_row_8 : ∀ j : Fin 10,
    k11t8p6.graph.Adj 8 j ↔ adjacencyTableLookup k11t8p6_adjacencyTable 8 j.val = true := by decide

private theorem k11t8p6_adjacency_row_9 : ∀ j : Fin 10,
    k11t8p6.graph.Adj 9 j ↔ adjacencyTableLookup k11t8p6_adjacencyTable 9 j.val = true := by decide

private theorem k11t8p6_adjacency_eq : ∀ i j : Fin 10,
    k11t8p6.graph.Adj i j ↔ adjacencyTableLookup k11t8p6_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t8p6_adjacency_row_0 j

  · exact k11t8p6_adjacency_row_1 j

  · exact k11t8p6_adjacency_row_2 j

  · exact k11t8p6_adjacency_row_3 j

  · exact k11t8p6_adjacency_row_4 j

  · exact k11t8p6_adjacency_row_5 j

  · exact k11t8p6_adjacency_row_6 j

  · exact k11t8p6_adjacency_row_7 j

  · exact k11t8p6_adjacency_row_8 j

  · exact k11t8p6_adjacency_row_9 j

private def k11t8p6_tableGraph : SimpleGraph (Fin 10) :=
  adjacencyTableGraph k11t8p6.graph k11t8p6_adjacencyTable k11t8p6_adjacency_eq

private instance k11t8p6_tableGraph_decidableAdj :
    DecidableRel k11t8p6_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t8p6_adjacencyTable i.val j.val = true))

private theorem k11t8p6_tableGraph_eq : k11t8p6_tableGraph = k11t8p6.graph :=
  adjacencyTableGraph_eq k11t8p6.graph k11t8p6_adjacencyTable k11t8p6_adjacency_eq

private def k11t8p6_state_0 : ForbiddenMatrix 10 :=
  fun i j => ((#[#[∅, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 5, Finset.Icc 1 9, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅],
    #[Finset.Icc 1 10, ∅, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 5, Finset.Icc 1 9, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅],
    #[Finset.Icc 1 10, Finset.Icc 1 10, ∅, Finset.Icc 1 10, Finset.Icc 1 5, Finset.Icc 1 9, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅],
    #[Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, ∅, Finset.Icc 1 5, Finset.Icc 1 9, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, Finset.Icc 1 9, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t8p6_decode_entry_0 : decode 12 2044 = Finset.Icc 2 10 := by decide

private theorem k11t8p6_decode_entry_1 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p6_decode_entry_2 : decode 12 2044 = Finset.Icc 2 10 := by decide

private theorem k11t8p6_decode_entry_3 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p6_decode_entry_4 : decode 12 2044 = Finset.Icc 2 10 := by decide

private theorem k11t8p6_decode_entry_5 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p6_decode_entry_6 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p6_decode_entry_7 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p6_decode_entry_8 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p6_decode_entry_9 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p6_decode_entry_10 : decode 12 2044 = Finset.Icc 2 10 := by decide

private theorem k11t8p6_decode_entry_11 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p6_decode_entry_12 : decode 12 2044 = Finset.Icc 2 10 := by decide

private theorem k11t8p6_decode_entry_13 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p6_decode_entry_14 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p6_decode_entry_15 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p6_decode_entry_16 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p6_decode_entry_17 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p6_decode_entry_18 : decode 12 2044 = Finset.Icc 2 10 := by decide

private theorem k11t8p6_decode_entry_19 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p6_decode_entry_20 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p6_decode_entry_21 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p6_decode_entry_22 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p6_decode_entry_23 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p6_decode_entry_24 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p6_decode_entry_25 : decode 12 1022 = Finset.Icc 1 9 := by decide

private theorem k11t8p6_decode_entry_26 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p6_decode_entry_27 : decode 12 62 = Finset.Icc 1 5 := by decide

private def k11t8p6_mask_entries_0 : List (TemplateData (Fin 10) × ℕ) := [(⟨0, 1, [], [], [], 2, 10⟩, 2044), (⟨0, 1, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩, 30), (⟨0, 2, [], [], [], 2, 10⟩, 2044), (⟨0, 2, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩, 30), (⟨0, 3, [], [], [], 2, 10⟩, 2044), (⟨0, 3, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩, 30), (⟨0, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩, 62), (⟨0, 5, [], [], [4], 1, 9⟩, 1022), (⟨0, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩, 62), (⟨0, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩, 62), (⟨1, 2, [], [], [], 2, 10⟩, 2044), (⟨1, 2, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩, 30), (⟨1, 3, [], [], [], 2, 10⟩, 2044), (⟨1, 3, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩, 30), (⟨1, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩, 62), (⟨1, 5, [], [], [4], 1, 9⟩, 1022), (⟨1, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩, 62), (⟨1, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩, 62), (⟨2, 3, [], [], [], 2, 10⟩, 2044), (⟨2, 3, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩, 30), (⟨2, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩, 62), (⟨2, 5, [], [], [4], 1, 9⟩, 1022), (⟨2, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩, 62), (⟨2, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩, 62), (⟨3, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩, 62), (⟨3, 5, [], [], [4], 1, 9⟩, 1022), (⟨3, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩, 62), (⟨3, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩, 62)]

private theorem k11t8p6_decode_entries_0 : ∀ Tb ∈ k11t8p6_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t8p6_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p6_decode_entry_0, k11t8p6_decode_entry_1, k11t8p6_decode_entry_2, k11t8p6_decode_entry_3, k11t8p6_decode_entry_4, k11t8p6_decode_entry_5, k11t8p6_decode_entry_6, k11t8p6_decode_entry_7, k11t8p6_decode_entry_8, k11t8p6_decode_entry_9, k11t8p6_decode_entry_10, k11t8p6_decode_entry_11, k11t8p6_decode_entry_12, k11t8p6_decode_entry_13, k11t8p6_decode_entry_14, k11t8p6_decode_entry_15, k11t8p6_decode_entry_16, k11t8p6_decode_entry_17, k11t8p6_decode_entry_18, k11t8p6_decode_entry_19, k11t8p6_decode_entry_20, k11t8p6_decode_entry_21, k11t8p6_decode_entry_22, k11t8p6_decode_entry_23, k11t8p6_decode_entry_24, k11t8p6_decode_entry_25, k11t8p6_decode_entry_26, k11t8p6_decode_entry_27⟩

private def k11t8p6_mask_block_0 : Fin 10 → Fin 10 → ℕ :=
  fun i j => ((#[#[0, 2046, 2046, 2046, 62, 1022, 62, 62, 0, 0],
    #[2046, 0, 2046, 2046, 62, 1022, 62, 62, 0, 0],
    #[2046, 2046, 0, 2046, 62, 1022, 62, 62, 0, 0],
    #[2046, 2046, 2046, 0, 62, 1022, 62, 62, 0, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0],
    #[1022, 1022, 1022, 1022, 0, 0, 0, 0, 0, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p6_mask_block_0_eq_row_0 : ∀ j : Fin 10, (templateMaskMatrix k11t8p6_mask_entries_0) 0 j = k11t8p6_mask_block_0 0 j := by decide

private theorem k11t8p6_mask_block_0_eq_row_1 : ∀ j : Fin 10, (templateMaskMatrix k11t8p6_mask_entries_0) 1 j = k11t8p6_mask_block_0 1 j := by decide

private theorem k11t8p6_mask_block_0_eq_row_2 : ∀ j : Fin 10, (templateMaskMatrix k11t8p6_mask_entries_0) 2 j = k11t8p6_mask_block_0 2 j := by decide

private theorem k11t8p6_mask_block_0_eq_row_3 : ∀ j : Fin 10, (templateMaskMatrix k11t8p6_mask_entries_0) 3 j = k11t8p6_mask_block_0 3 j := by decide

private theorem k11t8p6_mask_block_0_eq_row_4 : ∀ j : Fin 10, (templateMaskMatrix k11t8p6_mask_entries_0) 4 j = k11t8p6_mask_block_0 4 j := by decide

private theorem k11t8p6_mask_block_0_eq_row_5 : ∀ j : Fin 10, (templateMaskMatrix k11t8p6_mask_entries_0) 5 j = k11t8p6_mask_block_0 5 j := by decide

private theorem k11t8p6_mask_block_0_eq_row_6 : ∀ j : Fin 10, (templateMaskMatrix k11t8p6_mask_entries_0) 6 j = k11t8p6_mask_block_0 6 j := by decide

private theorem k11t8p6_mask_block_0_eq_row_7 : ∀ j : Fin 10, (templateMaskMatrix k11t8p6_mask_entries_0) 7 j = k11t8p6_mask_block_0 7 j := by decide

private theorem k11t8p6_mask_block_0_eq_row_8 : ∀ j : Fin 10, (templateMaskMatrix k11t8p6_mask_entries_0) 8 j = k11t8p6_mask_block_0 8 j := by decide

private theorem k11t8p6_mask_block_0_eq_row_9 : ∀ j : Fin 10, (templateMaskMatrix k11t8p6_mask_entries_0) 9 j = k11t8p6_mask_block_0 9 j := by decide

private theorem k11t8p6_mask_block_0_eq : (templateMaskMatrix k11t8p6_mask_entries_0) = k11t8p6_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t8p6_mask_block_0_eq_row_0 j

  · exact k11t8p6_mask_block_0_eq_row_1 j

  · exact k11t8p6_mask_block_0_eq_row_2 j

  · exact k11t8p6_mask_block_0_eq_row_3 j

  · exact k11t8p6_mask_block_0_eq_row_4 j

  · exact k11t8p6_mask_block_0_eq_row_5 j

  · exact k11t8p6_mask_block_0_eq_row_6 j

  · exact k11t8p6_mask_block_0_eq_row_7 j

  · exact k11t8p6_mask_block_0_eq_row_8 j

  · exact k11t8p6_mask_block_0_eq_row_9 j

private def k11t8p6_mask_entries : List (TemplateData (Fin 10) × ℕ) := k11t8p6_mask_entries_0

private theorem k11t8p6_decode_entries : ∀ Tb ∈ k11t8p6_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t8p6_decode_entries_0

private theorem k11t8p6_mask_entries_map : k11t8p6_mask_entries.map Prod.fst = k11t8p6.templates := by rfl

private def k11t8p6_template_mask : Fin 10 → Fin 10 → ℕ :=
  fun i j => ((#[#[0, 2046, 2046, 2046, 62, 1022, 62, 62, 0, 0],
    #[2046, 0, 2046, 2046, 62, 1022, 62, 62, 0, 0],
    #[2046, 2046, 0, 2046, 62, 1022, 62, 62, 0, 0],
    #[2046, 2046, 2046, 0, 62, 1022, 62, 62, 0, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0],
    #[1022, 1022, 1022, 1022, 0, 0, 0, 0, 0, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p6_mask_merged_eq_row_0 : ∀ j : Fin 10, (fun i j => k11t8p6_mask_block_0 i j) 0 j = k11t8p6_template_mask 0 j := by decide

private theorem k11t8p6_mask_merged_eq_row_1 : ∀ j : Fin 10, (fun i j => k11t8p6_mask_block_0 i j) 1 j = k11t8p6_template_mask 1 j := by decide

private theorem k11t8p6_mask_merged_eq_row_2 : ∀ j : Fin 10, (fun i j => k11t8p6_mask_block_0 i j) 2 j = k11t8p6_template_mask 2 j := by decide

private theorem k11t8p6_mask_merged_eq_row_3 : ∀ j : Fin 10, (fun i j => k11t8p6_mask_block_0 i j) 3 j = k11t8p6_template_mask 3 j := by decide

private theorem k11t8p6_mask_merged_eq_row_4 : ∀ j : Fin 10, (fun i j => k11t8p6_mask_block_0 i j) 4 j = k11t8p6_template_mask 4 j := by decide

private theorem k11t8p6_mask_merged_eq_row_5 : ∀ j : Fin 10, (fun i j => k11t8p6_mask_block_0 i j) 5 j = k11t8p6_template_mask 5 j := by decide

private theorem k11t8p6_mask_merged_eq_row_6 : ∀ j : Fin 10, (fun i j => k11t8p6_mask_block_0 i j) 6 j = k11t8p6_template_mask 6 j := by decide

private theorem k11t8p6_mask_merged_eq_row_7 : ∀ j : Fin 10, (fun i j => k11t8p6_mask_block_0 i j) 7 j = k11t8p6_template_mask 7 j := by decide

private theorem k11t8p6_mask_merged_eq_row_8 : ∀ j : Fin 10, (fun i j => k11t8p6_mask_block_0 i j) 8 j = k11t8p6_template_mask 8 j := by decide

private theorem k11t8p6_mask_merged_eq_row_9 : ∀ j : Fin 10, (fun i j => k11t8p6_mask_block_0 i j) 9 j = k11t8p6_template_mask 9 j := by decide

private theorem k11t8p6_mask_merged_eq : (fun i j => k11t8p6_mask_block_0 i j) = k11t8p6_template_mask := by
  funext i j
  fin_cases i

  · exact k11t8p6_mask_merged_eq_row_0 j

  · exact k11t8p6_mask_merged_eq_row_1 j

  · exact k11t8p6_mask_merged_eq_row_2 j

  · exact k11t8p6_mask_merged_eq_row_3 j

  · exact k11t8p6_mask_merged_eq_row_4 j

  · exact k11t8p6_mask_merged_eq_row_5 j

  · exact k11t8p6_mask_merged_eq_row_6 j

  · exact k11t8p6_mask_merged_eq_row_7 j

  · exact k11t8p6_mask_merged_eq_row_8 j

  · exact k11t8p6_mask_merged_eq_row_9 j

private theorem k11t8p6_template_mask_eq : templateMaskMatrix k11t8p6_mask_entries = k11t8p6_template_mask := by
  funext i j
  change templateMaskMatrix (k11t8p6_mask_entries_0) i j = _
  simp only [k11t8p6_mask_block_0_eq]
  exact congrFun (congrFun k11t8p6_mask_merged_eq i) j

private theorem k11t8p6_initial_decoded_eq_row_0 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p6_template_mask i j) ∪ requiredMatrix 11 k11t8p6.required i j) 0 j = k11t8p6_state_0 0 j := by decide

private theorem k11t8p6_initial_decoded_eq_row_1 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p6_template_mask i j) ∪ requiredMatrix 11 k11t8p6.required i j) 1 j = k11t8p6_state_0 1 j := by decide

private theorem k11t8p6_initial_decoded_eq_row_2 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p6_template_mask i j) ∪ requiredMatrix 11 k11t8p6.required i j) 2 j = k11t8p6_state_0 2 j := by decide

private theorem k11t8p6_initial_decoded_eq_row_3 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p6_template_mask i j) ∪ requiredMatrix 11 k11t8p6.required i j) 3 j = k11t8p6_state_0 3 j := by decide

private theorem k11t8p6_initial_decoded_eq_row_4 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p6_template_mask i j) ∪ requiredMatrix 11 k11t8p6.required i j) 4 j = k11t8p6_state_0 4 j := by decide

private theorem k11t8p6_initial_decoded_eq_row_5 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p6_template_mask i j) ∪ requiredMatrix 11 k11t8p6.required i j) 5 j = k11t8p6_state_0 5 j := by decide

private theorem k11t8p6_initial_decoded_eq_row_6 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p6_template_mask i j) ∪ requiredMatrix 11 k11t8p6.required i j) 6 j = k11t8p6_state_0 6 j := by decide

private theorem k11t8p6_initial_decoded_eq_row_7 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p6_template_mask i j) ∪ requiredMatrix 11 k11t8p6.required i j) 7 j = k11t8p6_state_0 7 j := by decide

private theorem k11t8p6_initial_decoded_eq_row_8 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p6_template_mask i j) ∪ requiredMatrix 11 k11t8p6.required i j) 8 j = k11t8p6_state_0 8 j := by decide

private theorem k11t8p6_initial_decoded_eq_row_9 : ∀ j : Fin 10, (fun i j => decode 12 (k11t8p6_template_mask i j) ∪ requiredMatrix 11 k11t8p6.required i j) 9 j = k11t8p6_state_0 9 j := by decide

private theorem k11t8p6_initial_decoded_eq : (fun i j => decode 12 (k11t8p6_template_mask i j) ∪ requiredMatrix 11 k11t8p6.required i j) = k11t8p6_state_0 := by
  funext i j
  fin_cases i

  · exact k11t8p6_initial_decoded_eq_row_0 j

  · exact k11t8p6_initial_decoded_eq_row_1 j

  · exact k11t8p6_initial_decoded_eq_row_2 j

  · exact k11t8p6_initial_decoded_eq_row_3 j

  · exact k11t8p6_initial_decoded_eq_row_4 j

  · exact k11t8p6_initial_decoded_eq_row_5 j

  · exact k11t8p6_initial_decoded_eq_row_6 j

  · exact k11t8p6_initial_decoded_eq_row_7 j

  · exact k11t8p6_initial_decoded_eq_row_8 j

  · exact k11t8p6_initial_decoded_eq_row_9 j

private theorem k11t8p6_initial_eq : k11t8p6.initialMatrix 11 = k11t8p6_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t8p6_mask_entries k11t8p6_decode_entries
  rw [k11t8p6_mask_entries_map, k11t8p6_template_mask_eq] at h
  funext i j
  change templateMatrix k11t8p6.templates i j ∪ requiredMatrix 11 k11t8p6.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t8p6_initial_decoded_eq i) j

private theorem k11t8p6_closure_0 : ClosureCheck k11t8p6.graph k11t8p6_state_0 11 8 [] := by trivial

private theorem k11t8p6_matrix_eq : k11t8p6.matrix 11 = k11t8p6_state_0 := by
  change closureMatrix (k11t8p6.initialMatrix 11) _ = _
  rw [k11t8p6_initial_eq]
  change closureMatrix k11t8p6_state_0 [] = _
  rfl

private theorem k11t8p6_part_0 : k11t8p6.chains.flatten = List.finRange _ := by decide

private theorem k11t8p6_part_1 : k11t8p6.chains.map List.length = ([[], [], [], [], [1], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t8p6_part_2 : k11t8p6.chains.map (fun l => l.map (fun i => decide (i ∈ k11t8p6.clique))) = ([[], [], [], [], [1], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k11t8p6_templates_item_0 : (⟨0, 1, [], [], [], 2, 10⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_1 : (⟨0, 1, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_2 : (⟨0, 2, [], [], [], 2, 10⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_3 : (⟨0, 2, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_4 : (⟨0, 3, [], [], [], 2, 10⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_5 : (⟨0, 3, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_6 : (⟨0, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_7 : (⟨0, 5, [], [], [4], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_8 : (⟨0, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_9 : (⟨0, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_10 : (⟨1, 2, [], [], [], 2, 10⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_11 : (⟨1, 2, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_12 : (⟨1, 3, [], [], [], 2, 10⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_13 : (⟨1, 3, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_14 : (⟨1, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_15 : (⟨1, 5, [], [], [4], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_16 : (⟨1, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_17 : (⟨1, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_18 : (⟨2, 3, [], [], [], 2, 10⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_19 : (⟨2, 3, [[4, 5, 6], [7, 8, 9]], [], [], 1, 4⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_20 : (⟨2, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_21 : (⟨2, 5, [], [], [4], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_22 : (⟨2, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_23 : (⟨2, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_24 : (⟨3, 4, [[7, 8, 9]], [], [5, 6], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_25 : (⟨3, 5, [], [], [4], 1, 9⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_26 : (⟨3, 6, [[7, 8, 9]], [], [5, 4], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_item_27 : (⟨3, 7, [[4, 5, 6]], [], [8, 9], 1, 5⟩ : TemplateData (Fin 10)).Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p6_tableGraph_eq]
  decide

private theorem k11t8p6_templates_fast_block_0_check : ∀ T ∈ k11t8p6_mask_entries_0.map Prod.fst, T.Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t8p6_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p6_templates_item_0, k11t8p6_templates_item_1, k11t8p6_templates_item_2, k11t8p6_templates_item_3, k11t8p6_templates_item_4, k11t8p6_templates_item_5, k11t8p6_templates_item_6, k11t8p6_templates_item_7, k11t8p6_templates_item_8, k11t8p6_templates_item_9, k11t8p6_templates_item_10, k11t8p6_templates_item_11, k11t8p6_templates_item_12, k11t8p6_templates_item_13, k11t8p6_templates_item_14, k11t8p6_templates_item_15, k11t8p6_templates_item_16, k11t8p6_templates_item_17, k11t8p6_templates_item_18, k11t8p6_templates_item_19, k11t8p6_templates_item_20, k11t8p6_templates_item_21, k11t8p6_templates_item_22, k11t8p6_templates_item_23, k11t8p6_templates_item_24, k11t8p6_templates_item_25, k11t8p6_templates_item_26, k11t8p6_templates_item_27⟩

private theorem k11t8p6_part_3 : ∀ T ∈ k11t8p6.templates, T.Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t8p6_mask_entries_0.map Prod.fst), T.Check k11t8p6.graph k11t8p6.clique 11 (patternAmount ([[], [], [], [], [1], [1]] : List (List ℕ))) (([[], [], [], [], [1], [1]] : List (List ℕ)).map List.length).sum
  exact k11t8p6_templates_fast_block_0_check

private theorem k11t8p6_part_4 : ∀ p ∈ k11t8p6.required, p.Check k11t8p6.graph 11 := by decide

private theorem k11t8p6_part_5 : ClosureCheck k11t8p6.graph (k11t8p6.initialMatrix 11) 11 8 k11t8p6.closure := by
  rw [k11t8p6_initial_eq]
  exact k11t8p6_closure_0

private theorem k11t8p6_part_6 : k11t8p6.bad.Check k11t8p6.graph (k11t8p6.matrix 11) 11 8 := by
  rw [k11t8p6_matrix_eq]
  decide

theorem k11t8p6_check : k11t8p6.Check 11 8 [[], [], [], [], [1], [1]] :=
  ⟨k11t8p6_part_0, k11t8p6_part_1, k11t8p6_part_2, k11t8p6_part_3, k11t8p6_part_4, k11t8p6_part_5, k11t8p6_part_6⟩
def k11t8p7 : LayoutCertificate 11 where
  chains := [[0], [1], [2], [3], [4, 5, 6], [7, 8, 9, 10]]
  clique := {0, 1, 2, 3, 4, 6, 7, 10}
  templates := [⟨0, 1, [], [], [], 3, 10⟩,
    ⟨0, 1, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩,
    ⟨0, 2, [], [], [], 3, 10⟩,
    ⟨0, 2, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩,
    ⟨0, 3, [], [], [], 3, 10⟩,
    ⟨0, 3, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩,
    ⟨0, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩,
    ⟨0, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩,
    ⟨0, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩,
    ⟨0, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩,
    ⟨0, 9, [], [], [8, 7], 1, 8⟩,
    ⟨1, 2, [], [], [], 3, 10⟩,
    ⟨1, 2, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩,
    ⟨1, 3, [], [], [], 3, 10⟩,
    ⟨1, 3, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩,
    ⟨1, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩,
    ⟨1, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩,
    ⟨1, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩,
    ⟨1, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩,
    ⟨1, 9, [], [], [8, 7], 1, 8⟩,
    ⟨2, 3, [], [], [], 3, 10⟩,
    ⟨2, 3, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩,
    ⟨2, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩,
    ⟨2, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩,
    ⟨2, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩,
    ⟨2, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩,
    ⟨2, 9, [], [], [8, 7], 1, 8⟩,
    ⟨3, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩,
    ⟨3, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩,
    ⟨3, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩,
    ⟨3, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩,
    ⟨3, 9, [], [], [8, 7], 1, 8⟩]
  required := []
  closure := []
  bad := ⟨none, {(9, 0), (0, 2), (1, 3), (2, 3), (3, 3)}⟩


private def k11t8p7_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, true, true, false, true, true, false, false, true],
    #[true, false, true, true, true, false, true, true, false, false, true],
    #[true, true, false, true, true, false, true, true, false, false, true],
    #[true, true, true, false, true, false, true, true, false, false, true],
    #[true, true, true, true, false, true, true, true, false, false, true],
    #[false, false, false, false, true, false, true, false, false, false, false],
    #[true, true, true, true, true, true, false, true, false, false, true],
    #[true, true, true, true, true, false, true, false, true, false, true],
    #[false, false, false, false, false, false, false, true, false, true, false],
    #[false, false, false, false, false, false, false, false, true, false, true],
    #[true, true, true, true, true, false, true, true, false, true, false]]

private theorem k11t8p7_adjacency_row_0 : ∀ j : Fin 11,
    k11t8p7.graph.Adj 0 j ↔ adjacencyTableLookup k11t8p7_adjacencyTable 0 j.val = true := by decide

private theorem k11t8p7_adjacency_row_1 : ∀ j : Fin 11,
    k11t8p7.graph.Adj 1 j ↔ adjacencyTableLookup k11t8p7_adjacencyTable 1 j.val = true := by decide

private theorem k11t8p7_adjacency_row_2 : ∀ j : Fin 11,
    k11t8p7.graph.Adj 2 j ↔ adjacencyTableLookup k11t8p7_adjacencyTable 2 j.val = true := by decide

private theorem k11t8p7_adjacency_row_3 : ∀ j : Fin 11,
    k11t8p7.graph.Adj 3 j ↔ adjacencyTableLookup k11t8p7_adjacencyTable 3 j.val = true := by decide

private theorem k11t8p7_adjacency_row_4 : ∀ j : Fin 11,
    k11t8p7.graph.Adj 4 j ↔ adjacencyTableLookup k11t8p7_adjacencyTable 4 j.val = true := by decide

private theorem k11t8p7_adjacency_row_5 : ∀ j : Fin 11,
    k11t8p7.graph.Adj 5 j ↔ adjacencyTableLookup k11t8p7_adjacencyTable 5 j.val = true := by decide

private theorem k11t8p7_adjacency_row_6 : ∀ j : Fin 11,
    k11t8p7.graph.Adj 6 j ↔ adjacencyTableLookup k11t8p7_adjacencyTable 6 j.val = true := by decide

private theorem k11t8p7_adjacency_row_7 : ∀ j : Fin 11,
    k11t8p7.graph.Adj 7 j ↔ adjacencyTableLookup k11t8p7_adjacencyTable 7 j.val = true := by decide

private theorem k11t8p7_adjacency_row_8 : ∀ j : Fin 11,
    k11t8p7.graph.Adj 8 j ↔ adjacencyTableLookup k11t8p7_adjacencyTable 8 j.val = true := by decide

private theorem k11t8p7_adjacency_row_9 : ∀ j : Fin 11,
    k11t8p7.graph.Adj 9 j ↔ adjacencyTableLookup k11t8p7_adjacencyTable 9 j.val = true := by decide

private theorem k11t8p7_adjacency_row_10 : ∀ j : Fin 11,
    k11t8p7.graph.Adj 10 j ↔ adjacencyTableLookup k11t8p7_adjacencyTable 10 j.val = true := by decide

private theorem k11t8p7_adjacency_eq : ∀ i j : Fin 11,
    k11t8p7.graph.Adj i j ↔ adjacencyTableLookup k11t8p7_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t8p7_adjacency_row_0 j

  · exact k11t8p7_adjacency_row_1 j

  · exact k11t8p7_adjacency_row_2 j

  · exact k11t8p7_adjacency_row_3 j

  · exact k11t8p7_adjacency_row_4 j

  · exact k11t8p7_adjacency_row_5 j

  · exact k11t8p7_adjacency_row_6 j

  · exact k11t8p7_adjacency_row_7 j

  · exact k11t8p7_adjacency_row_8 j

  · exact k11t8p7_adjacency_row_9 j

  · exact k11t8p7_adjacency_row_10 j

private def k11t8p7_tableGraph : SimpleGraph (Fin 11) :=
  adjacencyTableGraph k11t8p7.graph k11t8p7_adjacencyTable k11t8p7_adjacency_eq

private instance k11t8p7_tableGraph_decidableAdj :
    DecidableRel k11t8p7_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t8p7_adjacencyTable i.val j.val = true))

private theorem k11t8p7_tableGraph_eq : k11t8p7_tableGraph = k11t8p7.graph :=
  adjacencyTableGraph_eq k11t8p7.graph k11t8p7_adjacencyTable k11t8p7_adjacency_eq

private def k11t8p7_state_0 : ForbiddenMatrix 11 :=
  fun i j => ((#[#[∅, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 8, ∅],
    #[Finset.Icc 1 10, ∅, Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 8, ∅],
    #[Finset.Icc 1 10, Finset.Icc 1 10, ∅, Finset.Icc 1 10, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 8, ∅],
    #[Finset.Icc 1 10, Finset.Icc 1 10, Finset.Icc 1 10, ∅, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 8, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 8, Finset.Icc 1 8, Finset.Icc 1 8, Finset.Icc 1 8, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t8p7_decode_entry_0 : decode 12 2040 = Finset.Icc 3 10 := by decide

private theorem k11t8p7_decode_entry_1 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p7_decode_entry_2 : decode 12 2040 = Finset.Icc 3 10 := by decide

private theorem k11t8p7_decode_entry_3 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p7_decode_entry_4 : decode 12 2040 = Finset.Icc 3 10 := by decide

private theorem k11t8p7_decode_entry_5 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p7_decode_entry_6 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_7 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p7_decode_entry_8 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_9 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_10 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p7_decode_entry_11 : decode 12 2040 = Finset.Icc 3 10 := by decide

private theorem k11t8p7_decode_entry_12 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p7_decode_entry_13 : decode 12 2040 = Finset.Icc 3 10 := by decide

private theorem k11t8p7_decode_entry_14 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p7_decode_entry_15 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_16 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p7_decode_entry_17 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_18 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_19 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p7_decode_entry_20 : decode 12 2040 = Finset.Icc 3 10 := by decide

private theorem k11t8p7_decode_entry_21 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p7_decode_entry_22 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_23 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p7_decode_entry_24 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_25 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_26 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p7_decode_entry_27 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_28 : decode 12 62 = Finset.Icc 1 5 := by decide

private theorem k11t8p7_decode_entry_29 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_30 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p7_decode_entry_31 : decode 12 510 = Finset.Icc 1 8 := by decide

private def k11t8p7_mask_entries_0 : List (TemplateData (Fin 11) × ℕ) := [(⟨0, 1, [], [], [], 3, 10⟩, 2040), (⟨0, 1, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩, 14), (⟨0, 2, [], [], [], 3, 10⟩, 2040), (⟨0, 2, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩, 14), (⟨0, 3, [], [], [], 3, 10⟩, 2040), (⟨0, 3, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩, 14), (⟨0, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩, 30), (⟨0, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩, 62), (⟨0, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩, 30), (⟨0, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩, 30), (⟨0, 9, [], [], [8, 7], 1, 8⟩, 510), (⟨1, 2, [], [], [], 3, 10⟩, 2040), (⟨1, 2, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩, 14), (⟨1, 3, [], [], [], 3, 10⟩, 2040), (⟨1, 3, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩, 14), (⟨1, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩, 30), (⟨1, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩, 62), (⟨1, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩, 30), (⟨1, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩, 30), (⟨1, 9, [], [], [8, 7], 1, 8⟩, 510), (⟨2, 3, [], [], [], 3, 10⟩, 2040), (⟨2, 3, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩, 14), (⟨2, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩, 30), (⟨2, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩, 62), (⟨2, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩, 30), (⟨2, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩, 30), (⟨2, 9, [], [], [8, 7], 1, 8⟩, 510), (⟨3, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩, 30), (⟨3, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩, 62), (⟨3, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩, 30), (⟨3, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩, 30), (⟨3, 9, [], [], [8, 7], 1, 8⟩, 510)]

private theorem k11t8p7_decode_entries_0 : ∀ Tb ∈ k11t8p7_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t8p7_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p7_decode_entry_0, k11t8p7_decode_entry_1, k11t8p7_decode_entry_2, k11t8p7_decode_entry_3, k11t8p7_decode_entry_4, k11t8p7_decode_entry_5, k11t8p7_decode_entry_6, k11t8p7_decode_entry_7, k11t8p7_decode_entry_8, k11t8p7_decode_entry_9, k11t8p7_decode_entry_10, k11t8p7_decode_entry_11, k11t8p7_decode_entry_12, k11t8p7_decode_entry_13, k11t8p7_decode_entry_14, k11t8p7_decode_entry_15, k11t8p7_decode_entry_16, k11t8p7_decode_entry_17, k11t8p7_decode_entry_18, k11t8p7_decode_entry_19, k11t8p7_decode_entry_20, k11t8p7_decode_entry_21, k11t8p7_decode_entry_22, k11t8p7_decode_entry_23, k11t8p7_decode_entry_24, k11t8p7_decode_entry_25, k11t8p7_decode_entry_26, k11t8p7_decode_entry_27, k11t8p7_decode_entry_28, k11t8p7_decode_entry_29, k11t8p7_decode_entry_30, k11t8p7_decode_entry_31⟩

private def k11t8p7_mask_block_0 : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 2046, 2046, 2046, 30, 62, 30, 30, 0, 510, 0],
    #[2046, 0, 2046, 2046, 30, 62, 30, 30, 0, 510, 0],
    #[2046, 2046, 0, 2046, 30, 62, 30, 30, 0, 510, 0],
    #[2046, 2046, 2046, 0, 30, 62, 30, 30, 0, 510, 0],
    #[30, 30, 30, 30, 0, 0, 0, 0, 0, 0, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0, 0],
    #[30, 30, 30, 30, 0, 0, 0, 0, 0, 0, 0],
    #[30, 30, 30, 30, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[510, 510, 510, 510, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p7_mask_block_0_eq_row_0 : ∀ j : Fin 11, (templateMaskMatrix k11t8p7_mask_entries_0) 0 j = k11t8p7_mask_block_0 0 j := by decide

private theorem k11t8p7_mask_block_0_eq_row_1 : ∀ j : Fin 11, (templateMaskMatrix k11t8p7_mask_entries_0) 1 j = k11t8p7_mask_block_0 1 j := by decide

private theorem k11t8p7_mask_block_0_eq_row_2 : ∀ j : Fin 11, (templateMaskMatrix k11t8p7_mask_entries_0) 2 j = k11t8p7_mask_block_0 2 j := by decide

private theorem k11t8p7_mask_block_0_eq_row_3 : ∀ j : Fin 11, (templateMaskMatrix k11t8p7_mask_entries_0) 3 j = k11t8p7_mask_block_0 3 j := by decide

private theorem k11t8p7_mask_block_0_eq_row_4 : ∀ j : Fin 11, (templateMaskMatrix k11t8p7_mask_entries_0) 4 j = k11t8p7_mask_block_0 4 j := by decide

private theorem k11t8p7_mask_block_0_eq_row_5 : ∀ j : Fin 11, (templateMaskMatrix k11t8p7_mask_entries_0) 5 j = k11t8p7_mask_block_0 5 j := by decide

private theorem k11t8p7_mask_block_0_eq_row_6 : ∀ j : Fin 11, (templateMaskMatrix k11t8p7_mask_entries_0) 6 j = k11t8p7_mask_block_0 6 j := by decide

private theorem k11t8p7_mask_block_0_eq_row_7 : ∀ j : Fin 11, (templateMaskMatrix k11t8p7_mask_entries_0) 7 j = k11t8p7_mask_block_0 7 j := by decide

private theorem k11t8p7_mask_block_0_eq_row_8 : ∀ j : Fin 11, (templateMaskMatrix k11t8p7_mask_entries_0) 8 j = k11t8p7_mask_block_0 8 j := by decide

private theorem k11t8p7_mask_block_0_eq_row_9 : ∀ j : Fin 11, (templateMaskMatrix k11t8p7_mask_entries_0) 9 j = k11t8p7_mask_block_0 9 j := by decide

private theorem k11t8p7_mask_block_0_eq_row_10 : ∀ j : Fin 11, (templateMaskMatrix k11t8p7_mask_entries_0) 10 j = k11t8p7_mask_block_0 10 j := by decide

private theorem k11t8p7_mask_block_0_eq : (templateMaskMatrix k11t8p7_mask_entries_0) = k11t8p7_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t8p7_mask_block_0_eq_row_0 j

  · exact k11t8p7_mask_block_0_eq_row_1 j

  · exact k11t8p7_mask_block_0_eq_row_2 j

  · exact k11t8p7_mask_block_0_eq_row_3 j

  · exact k11t8p7_mask_block_0_eq_row_4 j

  · exact k11t8p7_mask_block_0_eq_row_5 j

  · exact k11t8p7_mask_block_0_eq_row_6 j

  · exact k11t8p7_mask_block_0_eq_row_7 j

  · exact k11t8p7_mask_block_0_eq_row_8 j

  · exact k11t8p7_mask_block_0_eq_row_9 j

  · exact k11t8p7_mask_block_0_eq_row_10 j

private def k11t8p7_mask_entries : List (TemplateData (Fin 11) × ℕ) := k11t8p7_mask_entries_0

private theorem k11t8p7_decode_entries : ∀ Tb ∈ k11t8p7_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t8p7_decode_entries_0

private theorem k11t8p7_mask_entries_map : k11t8p7_mask_entries.map Prod.fst = k11t8p7.templates := by rfl

private def k11t8p7_template_mask : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 2046, 2046, 2046, 30, 62, 30, 30, 0, 510, 0],
    #[2046, 0, 2046, 2046, 30, 62, 30, 30, 0, 510, 0],
    #[2046, 2046, 0, 2046, 30, 62, 30, 30, 0, 510, 0],
    #[2046, 2046, 2046, 0, 30, 62, 30, 30, 0, 510, 0],
    #[30, 30, 30, 30, 0, 0, 0, 0, 0, 0, 0],
    #[62, 62, 62, 62, 0, 0, 0, 0, 0, 0, 0],
    #[30, 30, 30, 30, 0, 0, 0, 0, 0, 0, 0],
    #[30, 30, 30, 30, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[510, 510, 510, 510, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p7_mask_merged_eq_row_0 : ∀ j : Fin 11, (fun i j => k11t8p7_mask_block_0 i j) 0 j = k11t8p7_template_mask 0 j := by decide

private theorem k11t8p7_mask_merged_eq_row_1 : ∀ j : Fin 11, (fun i j => k11t8p7_mask_block_0 i j) 1 j = k11t8p7_template_mask 1 j := by decide

private theorem k11t8p7_mask_merged_eq_row_2 : ∀ j : Fin 11, (fun i j => k11t8p7_mask_block_0 i j) 2 j = k11t8p7_template_mask 2 j := by decide

private theorem k11t8p7_mask_merged_eq_row_3 : ∀ j : Fin 11, (fun i j => k11t8p7_mask_block_0 i j) 3 j = k11t8p7_template_mask 3 j := by decide

private theorem k11t8p7_mask_merged_eq_row_4 : ∀ j : Fin 11, (fun i j => k11t8p7_mask_block_0 i j) 4 j = k11t8p7_template_mask 4 j := by decide

private theorem k11t8p7_mask_merged_eq_row_5 : ∀ j : Fin 11, (fun i j => k11t8p7_mask_block_0 i j) 5 j = k11t8p7_template_mask 5 j := by decide

private theorem k11t8p7_mask_merged_eq_row_6 : ∀ j : Fin 11, (fun i j => k11t8p7_mask_block_0 i j) 6 j = k11t8p7_template_mask 6 j := by decide

private theorem k11t8p7_mask_merged_eq_row_7 : ∀ j : Fin 11, (fun i j => k11t8p7_mask_block_0 i j) 7 j = k11t8p7_template_mask 7 j := by decide

private theorem k11t8p7_mask_merged_eq_row_8 : ∀ j : Fin 11, (fun i j => k11t8p7_mask_block_0 i j) 8 j = k11t8p7_template_mask 8 j := by decide

private theorem k11t8p7_mask_merged_eq_row_9 : ∀ j : Fin 11, (fun i j => k11t8p7_mask_block_0 i j) 9 j = k11t8p7_template_mask 9 j := by decide

private theorem k11t8p7_mask_merged_eq_row_10 : ∀ j : Fin 11, (fun i j => k11t8p7_mask_block_0 i j) 10 j = k11t8p7_template_mask 10 j := by decide

private theorem k11t8p7_mask_merged_eq : (fun i j => k11t8p7_mask_block_0 i j) = k11t8p7_template_mask := by
  funext i j
  fin_cases i

  · exact k11t8p7_mask_merged_eq_row_0 j

  · exact k11t8p7_mask_merged_eq_row_1 j

  · exact k11t8p7_mask_merged_eq_row_2 j

  · exact k11t8p7_mask_merged_eq_row_3 j

  · exact k11t8p7_mask_merged_eq_row_4 j

  · exact k11t8p7_mask_merged_eq_row_5 j

  · exact k11t8p7_mask_merged_eq_row_6 j

  · exact k11t8p7_mask_merged_eq_row_7 j

  · exact k11t8p7_mask_merged_eq_row_8 j

  · exact k11t8p7_mask_merged_eq_row_9 j

  · exact k11t8p7_mask_merged_eq_row_10 j

private theorem k11t8p7_template_mask_eq : templateMaskMatrix k11t8p7_mask_entries = k11t8p7_template_mask := by
  funext i j
  change templateMaskMatrix (k11t8p7_mask_entries_0) i j = _
  simp only [k11t8p7_mask_block_0_eq]
  exact congrFun (congrFun k11t8p7_mask_merged_eq i) j

private theorem k11t8p7_initial_decoded_eq_row_0 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) 0 j = k11t8p7_state_0 0 j := by decide

private theorem k11t8p7_initial_decoded_eq_row_1 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) 1 j = k11t8p7_state_0 1 j := by decide

private theorem k11t8p7_initial_decoded_eq_row_2 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) 2 j = k11t8p7_state_0 2 j := by decide

private theorem k11t8p7_initial_decoded_eq_row_3 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) 3 j = k11t8p7_state_0 3 j := by decide

private theorem k11t8p7_initial_decoded_eq_row_4 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) 4 j = k11t8p7_state_0 4 j := by decide

private theorem k11t8p7_initial_decoded_eq_row_5 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) 5 j = k11t8p7_state_0 5 j := by decide

private theorem k11t8p7_initial_decoded_eq_row_6 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) 6 j = k11t8p7_state_0 6 j := by decide

private theorem k11t8p7_initial_decoded_eq_row_7 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) 7 j = k11t8p7_state_0 7 j := by decide

private theorem k11t8p7_initial_decoded_eq_row_8 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) 8 j = k11t8p7_state_0 8 j := by decide

private theorem k11t8p7_initial_decoded_eq_row_9 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) 9 j = k11t8p7_state_0 9 j := by decide

private theorem k11t8p7_initial_decoded_eq_row_10 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) 10 j = k11t8p7_state_0 10 j := by decide

private theorem k11t8p7_initial_decoded_eq : (fun i j => decode 12 (k11t8p7_template_mask i j) ∪ requiredMatrix 11 k11t8p7.required i j) = k11t8p7_state_0 := by
  funext i j
  fin_cases i

  · exact k11t8p7_initial_decoded_eq_row_0 j

  · exact k11t8p7_initial_decoded_eq_row_1 j

  · exact k11t8p7_initial_decoded_eq_row_2 j

  · exact k11t8p7_initial_decoded_eq_row_3 j

  · exact k11t8p7_initial_decoded_eq_row_4 j

  · exact k11t8p7_initial_decoded_eq_row_5 j

  · exact k11t8p7_initial_decoded_eq_row_6 j

  · exact k11t8p7_initial_decoded_eq_row_7 j

  · exact k11t8p7_initial_decoded_eq_row_8 j

  · exact k11t8p7_initial_decoded_eq_row_9 j

  · exact k11t8p7_initial_decoded_eq_row_10 j

private theorem k11t8p7_initial_eq : k11t8p7.initialMatrix 11 = k11t8p7_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t8p7_mask_entries k11t8p7_decode_entries
  rw [k11t8p7_mask_entries_map, k11t8p7_template_mask_eq] at h
  funext i j
  change templateMatrix k11t8p7.templates i j ∪ requiredMatrix 11 k11t8p7.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t8p7_initial_decoded_eq i) j

private theorem k11t8p7_closure_0 : ClosureCheck k11t8p7.graph k11t8p7_state_0 11 8 [] := by trivial

private theorem k11t8p7_matrix_eq : k11t8p7.matrix 11 = k11t8p7_state_0 := by
  change closureMatrix (k11t8p7.initialMatrix 11) _ = _
  rw [k11t8p7_initial_eq]
  change closureMatrix k11t8p7_state_0 [] = _
  rfl

private theorem k11t8p7_part_0 : k11t8p7.chains.flatten = List.finRange _ := by decide

private theorem k11t8p7_part_1 : k11t8p7.chains.map List.length = ([[], [], [], [], [1], [2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t8p7_part_2 : k11t8p7.chains.map (fun l => l.map (fun i => decide (i ∈ k11t8p7.clique))) = ([[], [], [], [], [1], [2]] : List (List ℕ)).map profileMask := by decide

private theorem k11t8p7_templates_item_0 : (⟨0, 1, [], [], [], 3, 10⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_1 : (⟨0, 1, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_2 : (⟨0, 2, [], [], [], 3, 10⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_3 : (⟨0, 2, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_4 : (⟨0, 3, [], [], [], 3, 10⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_5 : (⟨0, 3, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_6 : (⟨0, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_7 : (⟨0, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_8 : (⟨0, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_9 : (⟨0, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_10 : (⟨0, 9, [], [], [8, 7], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_11 : (⟨1, 2, [], [], [], 3, 10⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_12 : (⟨1, 2, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_13 : (⟨1, 3, [], [], [], 3, 10⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_14 : (⟨1, 3, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_15 : (⟨1, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_16 : (⟨1, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_17 : (⟨1, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_18 : (⟨1, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_19 : (⟨1, 9, [], [], [8, 7], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_20 : (⟨2, 3, [], [], [], 3, 10⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_21 : (⟨2, 3, [[4, 5, 6], [7, 8, 9, 10]], [], [], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_22 : (⟨2, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_23 : (⟨2, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_24 : (⟨2, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_25 : (⟨2, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_26 : (⟨2, 9, [], [], [8, 7], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_27 : (⟨3, 4, [[7, 8, 9, 10]], [], [5, 6], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_28 : (⟨3, 5, [[7, 8, 9, 10]], [], [4], 1, 5⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_29 : (⟨3, 6, [[7, 8, 9, 10]], [], [5, 4], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_30 : (⟨3, 7, [[4, 5, 6]], [], [8, 9, 10], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_item_31 : (⟨3, 9, [], [], [8, 7], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p7_tableGraph_eq]
  decide

private theorem k11t8p7_templates_fast_block_0_check : ∀ T ∈ k11t8p7_mask_entries_0.map Prod.fst, T.Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t8p7_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p7_templates_item_0, k11t8p7_templates_item_1, k11t8p7_templates_item_2, k11t8p7_templates_item_3, k11t8p7_templates_item_4, k11t8p7_templates_item_5, k11t8p7_templates_item_6, k11t8p7_templates_item_7, k11t8p7_templates_item_8, k11t8p7_templates_item_9, k11t8p7_templates_item_10, k11t8p7_templates_item_11, k11t8p7_templates_item_12, k11t8p7_templates_item_13, k11t8p7_templates_item_14, k11t8p7_templates_item_15, k11t8p7_templates_item_16, k11t8p7_templates_item_17, k11t8p7_templates_item_18, k11t8p7_templates_item_19, k11t8p7_templates_item_20, k11t8p7_templates_item_21, k11t8p7_templates_item_22, k11t8p7_templates_item_23, k11t8p7_templates_item_24, k11t8p7_templates_item_25, k11t8p7_templates_item_26, k11t8p7_templates_item_27, k11t8p7_templates_item_28, k11t8p7_templates_item_29, k11t8p7_templates_item_30, k11t8p7_templates_item_31⟩

private theorem k11t8p7_part_3 : ∀ T ∈ k11t8p7.templates, T.Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t8p7_mask_entries_0.map Prod.fst), T.Check k11t8p7.graph k11t8p7.clique 11 (patternAmount ([[], [], [], [], [1], [2]] : List (List ℕ))) (([[], [], [], [], [1], [2]] : List (List ℕ)).map List.length).sum
  exact k11t8p7_templates_fast_block_0_check

private theorem k11t8p7_part_4 : ∀ p ∈ k11t8p7.required, p.Check k11t8p7.graph 11 := by decide

private theorem k11t8p7_part_5 : ClosureCheck k11t8p7.graph (k11t8p7.initialMatrix 11) 11 8 k11t8p7.closure := by
  rw [k11t8p7_initial_eq]
  exact k11t8p7_closure_0

private theorem k11t8p7_part_6 : k11t8p7.bad.Check k11t8p7.graph (k11t8p7.matrix 11) 11 8 := by
  rw [k11t8p7_matrix_eq]
  decide

theorem k11t8p7_check : k11t8p7.Check 11 8 [[], [], [], [], [1], [2]] :=
  ⟨k11t8p7_part_0, k11t8p7_part_1, k11t8p7_part_2, k11t8p7_part_3, k11t8p7_part_4, k11t8p7_part_5, k11t8p7_part_6⟩
def k11t8p8 : LayoutCertificate 11 where
  chains := [[0], [1], [2], [3], [4, 5, 6, 7, 8, 9, 10]]
  clique := {0, 1, 2, 3, 4, 6, 8, 10}
  templates := [⟨0, 1, [[4, 5, 6, 7, 8, 9, 10]], [], [], 1, 3⟩,
    ⟨0, 2, [[4, 5, 6, 7, 8, 9, 10]], [], [], 1, 3⟩,
    ⟨0, 3, [[4, 5, 6, 7, 8, 9, 10]], [], [], 1, 3⟩,
    ⟨0, 4, [], [], [5, 6, 7, 8, 9, 10], 1, 4⟩,
    ⟨0, 5, [[6, 7, 8]], [], [4], 1, 6⟩,
    ⟨0, 7, [], [], [6, 5, 4], 1, 7⟩,
    ⟨0, 9, [[4, 5, 6]], [], [8], 1, 6⟩,
    ⟨0, 10, [], [], [9, 8, 7, 6, 5, 4], 1, 4⟩,
    ⟨1, 5, [[6, 7, 8]], [], [4], 1, 6⟩,
    ⟨1, 7, [], [], [6, 5, 4], 1, 7⟩,
    ⟨1, 9, [[4, 5, 6]], [], [8], 1, 6⟩,
    ⟨2, 5, [[6, 7, 8]], [], [4], 1, 6⟩,
    ⟨2, 7, [], [], [6, 5, 4], 1, 7⟩,
    ⟨2, 9, [[4, 5, 6]], [], [8], 1, 6⟩,
    ⟨3, 5, [[6, 7, 8]], [], [4], 1, 6⟩,
    ⟨3, 7, [], [], [6, 5, 4], 1, 7⟩,
    ⟨3, 9, [[4, 5, 6]], [], [8], 1, 6⟩,
    ⟨4, 5, [], [], [6, 7, 8], 1, 7⟩,
    ⟨4, 7, [], [6, 5], [8], 1, 7⟩,
    ⟨4, 9, [], [6, 5], [8], 1, 7⟩,
    ⟨5, 6, [], [4], [7, 8], 1, 7⟩,
    ⟨5, 7, [], [4], [6], 1, 8⟩,
    ⟨5, 9, [], [4], [8], 1, 8⟩,
    ⟨6, 7, [], [4, 5], [8], 1, 7⟩,
    ⟨6, 9, [], [4, 5], [8], 1, 7⟩,
    ⟨7, 9, [], [6], [8], 1, 8⟩]
  required := []
  closure := []
  bad := ⟨none, {(1, 0), (5, 2), (0, 3), (7, 3), (9, 3)}⟩


private def k11t8p8_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, true, true, false, true, false, true, false, true],
    #[true, false, true, true, true, false, true, false, true, false, true],
    #[true, true, false, true, true, false, true, false, true, false, true],
    #[true, true, true, false, true, false, true, false, true, false, true],
    #[true, true, true, true, false, true, true, false, true, false, true],
    #[false, false, false, false, true, false, true, false, false, false, false],
    #[true, true, true, true, true, true, false, true, true, false, true],
    #[false, false, false, false, false, false, true, false, true, false, false],
    #[true, true, true, true, true, false, true, true, false, true, true],
    #[false, false, false, false, false, false, false, false, true, false, true],
    #[true, true, true, true, true, false, true, false, true, true, false]]

private theorem k11t8p8_adjacency_row_0 : ∀ j : Fin 11,
    k11t8p8.graph.Adj 0 j ↔ adjacencyTableLookup k11t8p8_adjacencyTable 0 j.val = true := by decide

private theorem k11t8p8_adjacency_row_1 : ∀ j : Fin 11,
    k11t8p8.graph.Adj 1 j ↔ adjacencyTableLookup k11t8p8_adjacencyTable 1 j.val = true := by decide

private theorem k11t8p8_adjacency_row_2 : ∀ j : Fin 11,
    k11t8p8.graph.Adj 2 j ↔ adjacencyTableLookup k11t8p8_adjacencyTable 2 j.val = true := by decide

private theorem k11t8p8_adjacency_row_3 : ∀ j : Fin 11,
    k11t8p8.graph.Adj 3 j ↔ adjacencyTableLookup k11t8p8_adjacencyTable 3 j.val = true := by decide

private theorem k11t8p8_adjacency_row_4 : ∀ j : Fin 11,
    k11t8p8.graph.Adj 4 j ↔ adjacencyTableLookup k11t8p8_adjacencyTable 4 j.val = true := by decide

private theorem k11t8p8_adjacency_row_5 : ∀ j : Fin 11,
    k11t8p8.graph.Adj 5 j ↔ adjacencyTableLookup k11t8p8_adjacencyTable 5 j.val = true := by decide

private theorem k11t8p8_adjacency_row_6 : ∀ j : Fin 11,
    k11t8p8.graph.Adj 6 j ↔ adjacencyTableLookup k11t8p8_adjacencyTable 6 j.val = true := by decide

private theorem k11t8p8_adjacency_row_7 : ∀ j : Fin 11,
    k11t8p8.graph.Adj 7 j ↔ adjacencyTableLookup k11t8p8_adjacencyTable 7 j.val = true := by decide

private theorem k11t8p8_adjacency_row_8 : ∀ j : Fin 11,
    k11t8p8.graph.Adj 8 j ↔ adjacencyTableLookup k11t8p8_adjacencyTable 8 j.val = true := by decide

private theorem k11t8p8_adjacency_row_9 : ∀ j : Fin 11,
    k11t8p8.graph.Adj 9 j ↔ adjacencyTableLookup k11t8p8_adjacencyTable 9 j.val = true := by decide

private theorem k11t8p8_adjacency_row_10 : ∀ j : Fin 11,
    k11t8p8.graph.Adj 10 j ↔ adjacencyTableLookup k11t8p8_adjacencyTable 10 j.val = true := by decide

private theorem k11t8p8_adjacency_eq : ∀ i j : Fin 11,
    k11t8p8.graph.Adj i j ↔ adjacencyTableLookup k11t8p8_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t8p8_adjacency_row_0 j

  · exact k11t8p8_adjacency_row_1 j

  · exact k11t8p8_adjacency_row_2 j

  · exact k11t8p8_adjacency_row_3 j

  · exact k11t8p8_adjacency_row_4 j

  · exact k11t8p8_adjacency_row_5 j

  · exact k11t8p8_adjacency_row_6 j

  · exact k11t8p8_adjacency_row_7 j

  · exact k11t8p8_adjacency_row_8 j

  · exact k11t8p8_adjacency_row_9 j

  · exact k11t8p8_adjacency_row_10 j

private def k11t8p8_tableGraph : SimpleGraph (Fin 11) :=
  adjacencyTableGraph k11t8p8.graph k11t8p8_adjacencyTable k11t8p8_adjacency_eq

private instance k11t8p8_tableGraph_decidableAdj :
    DecidableRel k11t8p8_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t8p8_adjacencyTable i.val j.val = true))

private theorem k11t8p8_tableGraph_eq : k11t8p8_tableGraph = k11t8p8.graph :=
  adjacencyTableGraph_eq k11t8p8.graph k11t8p8_adjacencyTable k11t8p8_adjacency_eq

private def k11t8p8_state_0 : ForbiddenMatrix 11 :=
  fun i j => ((#[#[∅, {1, 2, 3}, {1, 2, 3}, {1, 2, 3}, Finset.Icc 1 4, Finset.Icc 1 6, ∅, Finset.Icc 1 7, ∅, Finset.Icc 1 6, Finset.Icc 1 4],
    #[{1, 2, 3}, ∅, ∅, ∅, ∅, Finset.Icc 1 6, ∅, Finset.Icc 1 7, ∅, Finset.Icc 1 6, ∅],
    #[{1, 2, 3}, ∅, ∅, ∅, ∅, Finset.Icc 1 6, ∅, Finset.Icc 1 7, ∅, Finset.Icc 1 6, ∅],
    #[{1, 2, 3}, ∅, ∅, ∅, ∅, Finset.Icc 1 6, ∅, Finset.Icc 1 7, ∅, Finset.Icc 1 6, ∅],
    #[Finset.Icc 1 4, ∅, ∅, ∅, ∅, Finset.Icc 1 7, ∅, Finset.Icc 1 7, ∅, Finset.Icc 1 7, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 7, ∅, Finset.Icc 1 7, Finset.Icc 1 8, ∅, Finset.Icc 1 8, ∅],
    #[∅, ∅, ∅, ∅, ∅, Finset.Icc 1 7, ∅, Finset.Icc 1 7, ∅, Finset.Icc 1 7, ∅],
    #[Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 7, Finset.Icc 1 8, Finset.Icc 1 7, ∅, ∅, Finset.Icc 1 8, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 7, Finset.Icc 1 8, Finset.Icc 1 7, Finset.Icc 1 8, ∅, ∅, ∅],
    #[Finset.Icc 1 4, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t8p8_decode_entry_0 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p8_decode_entry_1 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p8_decode_entry_2 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p8_decode_entry_3 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p8_decode_entry_4 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p8_decode_entry_5 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p8_decode_entry_6 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p8_decode_entry_7 : decode 12 30 = Finset.Icc 1 4 := by decide

private theorem k11t8p8_decode_entry_8 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p8_decode_entry_9 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p8_decode_entry_10 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p8_decode_entry_11 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p8_decode_entry_12 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p8_decode_entry_13 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p8_decode_entry_14 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p8_decode_entry_15 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p8_decode_entry_16 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p8_decode_entry_17 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p8_decode_entry_18 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p8_decode_entry_19 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p8_decode_entry_20 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p8_decode_entry_21 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p8_decode_entry_22 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p8_decode_entry_23 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p8_decode_entry_24 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p8_decode_entry_25 : decode 12 510 = Finset.Icc 1 8 := by decide

private def k11t8p8_mask_entries_0 : List (TemplateData (Fin 11) × ℕ) := [(⟨0, 1, [[4, 5, 6, 7, 8, 9, 10]], [], [], 1, 3⟩, 14), (⟨0, 2, [[4, 5, 6, 7, 8, 9, 10]], [], [], 1, 3⟩, 14), (⟨0, 3, [[4, 5, 6, 7, 8, 9, 10]], [], [], 1, 3⟩, 14), (⟨0, 4, [], [], [5, 6, 7, 8, 9, 10], 1, 4⟩, 30), (⟨0, 5, [[6, 7, 8]], [], [4], 1, 6⟩, 126), (⟨0, 7, [], [], [6, 5, 4], 1, 7⟩, 254), (⟨0, 9, [[4, 5, 6]], [], [8], 1, 6⟩, 126), (⟨0, 10, [], [], [9, 8, 7, 6, 5, 4], 1, 4⟩, 30), (⟨1, 5, [[6, 7, 8]], [], [4], 1, 6⟩, 126), (⟨1, 7, [], [], [6, 5, 4], 1, 7⟩, 254), (⟨1, 9, [[4, 5, 6]], [], [8], 1, 6⟩, 126), (⟨2, 5, [[6, 7, 8]], [], [4], 1, 6⟩, 126), (⟨2, 7, [], [], [6, 5, 4], 1, 7⟩, 254), (⟨2, 9, [[4, 5, 6]], [], [8], 1, 6⟩, 126), (⟨3, 5, [[6, 7, 8]], [], [4], 1, 6⟩, 126), (⟨3, 7, [], [], [6, 5, 4], 1, 7⟩, 254), (⟨3, 9, [[4, 5, 6]], [], [8], 1, 6⟩, 126), (⟨4, 5, [], [], [6, 7, 8], 1, 7⟩, 254), (⟨4, 7, [], [6, 5], [8], 1, 7⟩, 254), (⟨4, 9, [], [6, 5], [8], 1, 7⟩, 254), (⟨5, 6, [], [4], [7, 8], 1, 7⟩, 254), (⟨5, 7, [], [4], [6], 1, 8⟩, 510), (⟨5, 9, [], [4], [8], 1, 8⟩, 510), (⟨6, 7, [], [4, 5], [8], 1, 7⟩, 254), (⟨6, 9, [], [4, 5], [8], 1, 7⟩, 254), (⟨7, 9, [], [6], [8], 1, 8⟩, 510)]

private theorem k11t8p8_decode_entries_0 : ∀ Tb ∈ k11t8p8_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t8p8_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p8_decode_entry_0, k11t8p8_decode_entry_1, k11t8p8_decode_entry_2, k11t8p8_decode_entry_3, k11t8p8_decode_entry_4, k11t8p8_decode_entry_5, k11t8p8_decode_entry_6, k11t8p8_decode_entry_7, k11t8p8_decode_entry_8, k11t8p8_decode_entry_9, k11t8p8_decode_entry_10, k11t8p8_decode_entry_11, k11t8p8_decode_entry_12, k11t8p8_decode_entry_13, k11t8p8_decode_entry_14, k11t8p8_decode_entry_15, k11t8p8_decode_entry_16, k11t8p8_decode_entry_17, k11t8p8_decode_entry_18, k11t8p8_decode_entry_19, k11t8p8_decode_entry_20, k11t8p8_decode_entry_21, k11t8p8_decode_entry_22, k11t8p8_decode_entry_23, k11t8p8_decode_entry_24, k11t8p8_decode_entry_25⟩

private def k11t8p8_mask_block_0 : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 14, 14, 14, 30, 126, 0, 254, 0, 126, 30],
    #[14, 0, 0, 0, 0, 126, 0, 254, 0, 126, 0],
    #[14, 0, 0, 0, 0, 126, 0, 254, 0, 126, 0],
    #[14, 0, 0, 0, 0, 126, 0, 254, 0, 126, 0],
    #[30, 0, 0, 0, 0, 254, 0, 254, 0, 254, 0],
    #[126, 126, 126, 126, 254, 0, 254, 510, 0, 510, 0],
    #[0, 0, 0, 0, 0, 254, 0, 254, 0, 254, 0],
    #[254, 254, 254, 254, 254, 510, 254, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[126, 126, 126, 126, 254, 510, 254, 510, 0, 0, 0],
    #[30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p8_mask_block_0_eq_row_0 : ∀ j : Fin 11, (templateMaskMatrix k11t8p8_mask_entries_0) 0 j = k11t8p8_mask_block_0 0 j := by decide

private theorem k11t8p8_mask_block_0_eq_row_1 : ∀ j : Fin 11, (templateMaskMatrix k11t8p8_mask_entries_0) 1 j = k11t8p8_mask_block_0 1 j := by decide

private theorem k11t8p8_mask_block_0_eq_row_2 : ∀ j : Fin 11, (templateMaskMatrix k11t8p8_mask_entries_0) 2 j = k11t8p8_mask_block_0 2 j := by decide

private theorem k11t8p8_mask_block_0_eq_row_3 : ∀ j : Fin 11, (templateMaskMatrix k11t8p8_mask_entries_0) 3 j = k11t8p8_mask_block_0 3 j := by decide

private theorem k11t8p8_mask_block_0_eq_row_4 : ∀ j : Fin 11, (templateMaskMatrix k11t8p8_mask_entries_0) 4 j = k11t8p8_mask_block_0 4 j := by decide

private theorem k11t8p8_mask_block_0_eq_row_5 : ∀ j : Fin 11, (templateMaskMatrix k11t8p8_mask_entries_0) 5 j = k11t8p8_mask_block_0 5 j := by decide

private theorem k11t8p8_mask_block_0_eq_row_6 : ∀ j : Fin 11, (templateMaskMatrix k11t8p8_mask_entries_0) 6 j = k11t8p8_mask_block_0 6 j := by decide

private theorem k11t8p8_mask_block_0_eq_row_7 : ∀ j : Fin 11, (templateMaskMatrix k11t8p8_mask_entries_0) 7 j = k11t8p8_mask_block_0 7 j := by decide

private theorem k11t8p8_mask_block_0_eq_row_8 : ∀ j : Fin 11, (templateMaskMatrix k11t8p8_mask_entries_0) 8 j = k11t8p8_mask_block_0 8 j := by decide

private theorem k11t8p8_mask_block_0_eq_row_9 : ∀ j : Fin 11, (templateMaskMatrix k11t8p8_mask_entries_0) 9 j = k11t8p8_mask_block_0 9 j := by decide

private theorem k11t8p8_mask_block_0_eq_row_10 : ∀ j : Fin 11, (templateMaskMatrix k11t8p8_mask_entries_0) 10 j = k11t8p8_mask_block_0 10 j := by decide

private theorem k11t8p8_mask_block_0_eq : (templateMaskMatrix k11t8p8_mask_entries_0) = k11t8p8_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t8p8_mask_block_0_eq_row_0 j

  · exact k11t8p8_mask_block_0_eq_row_1 j

  · exact k11t8p8_mask_block_0_eq_row_2 j

  · exact k11t8p8_mask_block_0_eq_row_3 j

  · exact k11t8p8_mask_block_0_eq_row_4 j

  · exact k11t8p8_mask_block_0_eq_row_5 j

  · exact k11t8p8_mask_block_0_eq_row_6 j

  · exact k11t8p8_mask_block_0_eq_row_7 j

  · exact k11t8p8_mask_block_0_eq_row_8 j

  · exact k11t8p8_mask_block_0_eq_row_9 j

  · exact k11t8p8_mask_block_0_eq_row_10 j

private def k11t8p8_mask_entries : List (TemplateData (Fin 11) × ℕ) := k11t8p8_mask_entries_0

private theorem k11t8p8_decode_entries : ∀ Tb ∈ k11t8p8_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t8p8_decode_entries_0

private theorem k11t8p8_mask_entries_map : k11t8p8_mask_entries.map Prod.fst = k11t8p8.templates := by rfl

private def k11t8p8_template_mask : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 14, 14, 14, 30, 126, 0, 254, 0, 126, 30],
    #[14, 0, 0, 0, 0, 126, 0, 254, 0, 126, 0],
    #[14, 0, 0, 0, 0, 126, 0, 254, 0, 126, 0],
    #[14, 0, 0, 0, 0, 126, 0, 254, 0, 126, 0],
    #[30, 0, 0, 0, 0, 254, 0, 254, 0, 254, 0],
    #[126, 126, 126, 126, 254, 0, 254, 510, 0, 510, 0],
    #[0, 0, 0, 0, 0, 254, 0, 254, 0, 254, 0],
    #[254, 254, 254, 254, 254, 510, 254, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[126, 126, 126, 126, 254, 510, 254, 510, 0, 0, 0],
    #[30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p8_mask_merged_eq_row_0 : ∀ j : Fin 11, (fun i j => k11t8p8_mask_block_0 i j) 0 j = k11t8p8_template_mask 0 j := by decide

private theorem k11t8p8_mask_merged_eq_row_1 : ∀ j : Fin 11, (fun i j => k11t8p8_mask_block_0 i j) 1 j = k11t8p8_template_mask 1 j := by decide

private theorem k11t8p8_mask_merged_eq_row_2 : ∀ j : Fin 11, (fun i j => k11t8p8_mask_block_0 i j) 2 j = k11t8p8_template_mask 2 j := by decide

private theorem k11t8p8_mask_merged_eq_row_3 : ∀ j : Fin 11, (fun i j => k11t8p8_mask_block_0 i j) 3 j = k11t8p8_template_mask 3 j := by decide

private theorem k11t8p8_mask_merged_eq_row_4 : ∀ j : Fin 11, (fun i j => k11t8p8_mask_block_0 i j) 4 j = k11t8p8_template_mask 4 j := by decide

private theorem k11t8p8_mask_merged_eq_row_5 : ∀ j : Fin 11, (fun i j => k11t8p8_mask_block_0 i j) 5 j = k11t8p8_template_mask 5 j := by decide

private theorem k11t8p8_mask_merged_eq_row_6 : ∀ j : Fin 11, (fun i j => k11t8p8_mask_block_0 i j) 6 j = k11t8p8_template_mask 6 j := by decide

private theorem k11t8p8_mask_merged_eq_row_7 : ∀ j : Fin 11, (fun i j => k11t8p8_mask_block_0 i j) 7 j = k11t8p8_template_mask 7 j := by decide

private theorem k11t8p8_mask_merged_eq_row_8 : ∀ j : Fin 11, (fun i j => k11t8p8_mask_block_0 i j) 8 j = k11t8p8_template_mask 8 j := by decide

private theorem k11t8p8_mask_merged_eq_row_9 : ∀ j : Fin 11, (fun i j => k11t8p8_mask_block_0 i j) 9 j = k11t8p8_template_mask 9 j := by decide

private theorem k11t8p8_mask_merged_eq_row_10 : ∀ j : Fin 11, (fun i j => k11t8p8_mask_block_0 i j) 10 j = k11t8p8_template_mask 10 j := by decide

private theorem k11t8p8_mask_merged_eq : (fun i j => k11t8p8_mask_block_0 i j) = k11t8p8_template_mask := by
  funext i j
  fin_cases i

  · exact k11t8p8_mask_merged_eq_row_0 j

  · exact k11t8p8_mask_merged_eq_row_1 j

  · exact k11t8p8_mask_merged_eq_row_2 j

  · exact k11t8p8_mask_merged_eq_row_3 j

  · exact k11t8p8_mask_merged_eq_row_4 j

  · exact k11t8p8_mask_merged_eq_row_5 j

  · exact k11t8p8_mask_merged_eq_row_6 j

  · exact k11t8p8_mask_merged_eq_row_7 j

  · exact k11t8p8_mask_merged_eq_row_8 j

  · exact k11t8p8_mask_merged_eq_row_9 j

  · exact k11t8p8_mask_merged_eq_row_10 j

private theorem k11t8p8_template_mask_eq : templateMaskMatrix k11t8p8_mask_entries = k11t8p8_template_mask := by
  funext i j
  change templateMaskMatrix (k11t8p8_mask_entries_0) i j = _
  simp only [k11t8p8_mask_block_0_eq]
  exact congrFun (congrFun k11t8p8_mask_merged_eq i) j

private theorem k11t8p8_initial_decoded_eq_row_0 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) 0 j = k11t8p8_state_0 0 j := by decide

private theorem k11t8p8_initial_decoded_eq_row_1 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) 1 j = k11t8p8_state_0 1 j := by decide

private theorem k11t8p8_initial_decoded_eq_row_2 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) 2 j = k11t8p8_state_0 2 j := by decide

private theorem k11t8p8_initial_decoded_eq_row_3 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) 3 j = k11t8p8_state_0 3 j := by decide

private theorem k11t8p8_initial_decoded_eq_row_4 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) 4 j = k11t8p8_state_0 4 j := by decide

private theorem k11t8p8_initial_decoded_eq_row_5 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) 5 j = k11t8p8_state_0 5 j := by decide

private theorem k11t8p8_initial_decoded_eq_row_6 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) 6 j = k11t8p8_state_0 6 j := by decide

private theorem k11t8p8_initial_decoded_eq_row_7 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) 7 j = k11t8p8_state_0 7 j := by decide

private theorem k11t8p8_initial_decoded_eq_row_8 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) 8 j = k11t8p8_state_0 8 j := by decide

private theorem k11t8p8_initial_decoded_eq_row_9 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) 9 j = k11t8p8_state_0 9 j := by decide

private theorem k11t8p8_initial_decoded_eq_row_10 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) 10 j = k11t8p8_state_0 10 j := by decide

private theorem k11t8p8_initial_decoded_eq : (fun i j => decode 12 (k11t8p8_template_mask i j) ∪ requiredMatrix 11 k11t8p8.required i j) = k11t8p8_state_0 := by
  funext i j
  fin_cases i

  · exact k11t8p8_initial_decoded_eq_row_0 j

  · exact k11t8p8_initial_decoded_eq_row_1 j

  · exact k11t8p8_initial_decoded_eq_row_2 j

  · exact k11t8p8_initial_decoded_eq_row_3 j

  · exact k11t8p8_initial_decoded_eq_row_4 j

  · exact k11t8p8_initial_decoded_eq_row_5 j

  · exact k11t8p8_initial_decoded_eq_row_6 j

  · exact k11t8p8_initial_decoded_eq_row_7 j

  · exact k11t8p8_initial_decoded_eq_row_8 j

  · exact k11t8p8_initial_decoded_eq_row_9 j

  · exact k11t8p8_initial_decoded_eq_row_10 j

private theorem k11t8p8_initial_eq : k11t8p8.initialMatrix 11 = k11t8p8_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t8p8_mask_entries k11t8p8_decode_entries
  rw [k11t8p8_mask_entries_map, k11t8p8_template_mask_eq] at h
  funext i j
  change templateMatrix k11t8p8.templates i j ∪ requiredMatrix 11 k11t8p8.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t8p8_initial_decoded_eq i) j

private theorem k11t8p8_closure_0 : ClosureCheck k11t8p8.graph k11t8p8_state_0 11 8 [] := by trivial

private theorem k11t8p8_matrix_eq : k11t8p8.matrix 11 = k11t8p8_state_0 := by
  change closureMatrix (k11t8p8.initialMatrix 11) _ = _
  rw [k11t8p8_initial_eq]
  change closureMatrix k11t8p8_state_0 [] = _
  rfl

private theorem k11t8p8_part_0 : k11t8p8.chains.flatten = List.finRange _ := by decide

private theorem k11t8p8_part_1 : k11t8p8.chains.map List.length = ([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t8p8_part_2 : k11t8p8.chains.map (fun l => l.map (fun i => decide (i ∈ k11t8p8.clique))) = ([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k11t8p8_templates_item_0 : (⟨0, 1, [[4, 5, 6, 7, 8, 9, 10]], [], [], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_1 : (⟨0, 2, [[4, 5, 6, 7, 8, 9, 10]], [], [], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_2 : (⟨0, 3, [[4, 5, 6, 7, 8, 9, 10]], [], [], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_3 : (⟨0, 4, [], [], [5, 6, 7, 8, 9, 10], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_4 : (⟨0, 5, [[6, 7, 8]], [], [4], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_5 : (⟨0, 7, [], [], [6, 5, 4], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_6 : (⟨0, 9, [[4, 5, 6]], [], [8], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_7 : (⟨0, 10, [], [], [9, 8, 7, 6, 5, 4], 1, 4⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_8 : (⟨1, 5, [[6, 7, 8]], [], [4], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_9 : (⟨1, 7, [], [], [6, 5, 4], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_10 : (⟨1, 9, [[4, 5, 6]], [], [8], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_11 : (⟨2, 5, [[6, 7, 8]], [], [4], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_12 : (⟨2, 7, [], [], [6, 5, 4], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_13 : (⟨2, 9, [[4, 5, 6]], [], [8], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_14 : (⟨3, 5, [[6, 7, 8]], [], [4], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_15 : (⟨3, 7, [], [], [6, 5, 4], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_16 : (⟨3, 9, [[4, 5, 6]], [], [8], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_17 : (⟨4, 5, [], [], [6, 7, 8], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_18 : (⟨4, 7, [], [6, 5], [8], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_19 : (⟨4, 9, [], [6, 5], [8], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_20 : (⟨5, 6, [], [4], [7, 8], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_21 : (⟨5, 7, [], [4], [6], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_22 : (⟨5, 9, [], [4], [8], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_23 : (⟨6, 7, [], [4, 5], [8], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_24 : (⟨6, 9, [], [4, 5], [8], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_item_25 : (⟨7, 9, [], [6], [8], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p8_tableGraph_eq]
  decide

private theorem k11t8p8_templates_fast_block_0_check : ∀ T ∈ k11t8p8_mask_entries_0.map Prod.fst, T.Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t8p8_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p8_templates_item_0, k11t8p8_templates_item_1, k11t8p8_templates_item_2, k11t8p8_templates_item_3, k11t8p8_templates_item_4, k11t8p8_templates_item_5, k11t8p8_templates_item_6, k11t8p8_templates_item_7, k11t8p8_templates_item_8, k11t8p8_templates_item_9, k11t8p8_templates_item_10, k11t8p8_templates_item_11, k11t8p8_templates_item_12, k11t8p8_templates_item_13, k11t8p8_templates_item_14, k11t8p8_templates_item_15, k11t8p8_templates_item_16, k11t8p8_templates_item_17, k11t8p8_templates_item_18, k11t8p8_templates_item_19, k11t8p8_templates_item_20, k11t8p8_templates_item_21, k11t8p8_templates_item_22, k11t8p8_templates_item_23, k11t8p8_templates_item_24, k11t8p8_templates_item_25⟩

private theorem k11t8p8_part_3 : ∀ T ∈ k11t8p8.templates, T.Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t8p8_mask_entries_0.map Prod.fst), T.Check k11t8p8.graph k11t8p8.clique 11 (patternAmount ([[], [], [], [], [1, 1, 1]] : List (List ℕ))) (([[], [], [], [], [1, 1, 1]] : List (List ℕ)).map List.length).sum
  exact k11t8p8_templates_fast_block_0_check

private theorem k11t8p8_part_4 : ∀ p ∈ k11t8p8.required, p.Check k11t8p8.graph 11 := by decide

private theorem k11t8p8_part_5 : ClosureCheck k11t8p8.graph (k11t8p8.initialMatrix 11) 11 8 k11t8p8.closure := by
  rw [k11t8p8_initial_eq]
  exact k11t8p8_closure_0

private theorem k11t8p8_part_6 : k11t8p8.bad.Check k11t8p8.graph (k11t8p8.matrix 11) 11 8 := by
  rw [k11t8p8_matrix_eq]
  decide

theorem k11t8p8_check : k11t8p8.Check 11 8 [[], [], [], [], [1, 1, 1]] :=
  ⟨k11t8p8_part_0, k11t8p8_part_1, k11t8p8_part_2, k11t8p8_part_3, k11t8p8_part_4, k11t8p8_part_5, k11t8p8_part_6⟩
def k11t8p9 : LayoutCertificate 11 where
  chains := [[0], [1], [2], [3, 4, 5], [6, 7, 8, 9, 10]]
  clique := {0, 1, 2, 3, 5, 6, 8, 10}
  templates := [⟨0, 1, [[3, 4, 5]], [], [], 2, 7⟩,
    ⟨0, 1, [[3, 4, 5], [6, 7, 8, 9, 10]], [], [], 1, 2⟩,
    ⟨0, 2, [[3, 4, 5], [6, 7, 8, 9, 10]], [], [], 1, 2⟩,
    ⟨0, 3, [[6, 7, 8, 9, 10]], [], [4, 5], 1, 3⟩,
    ⟨0, 4, [[6, 7, 8]], [], [3], 1, 6⟩,
    ⟨0, 5, [[6, 7, 8, 9, 10]], [], [4, 3], 1, 3⟩,
    ⟨0, 6, [[3, 4, 5]], [], [7, 8, 9, 10], 1, 3⟩,
    ⟨0, 7, [[3, 4, 5]], [], [6], 1, 6⟩,
    ⟨0, 9, [[3, 4, 5]], [], [8], 1, 6⟩,
    ⟨1, 4, [[6, 7, 8]], [], [3], 1, 6⟩,
    ⟨1, 7, [[3, 4, 5]], [], [6], 1, 6⟩,
    ⟨1, 9, [[3, 4, 5]], [], [8], 1, 6⟩,
    ⟨2, 4, [[6, 7, 8]], [], [3], 1, 6⟩,
    ⟨2, 7, [[3, 4, 5]], [], [6], 1, 6⟩,
    ⟨2, 9, [[3, 4, 5]], [], [8], 1, 6⟩,
    ⟨3, 4, [[6, 7, 8]], [], [5], 1, 6⟩,
    ⟨3, 7, [], [5, 4], [6], 1, 7⟩,
    ⟨3, 9, [], [5, 4], [8], 1, 7⟩,
    ⟨4, 5, [[6, 7, 8]], [3], [], 1, 6⟩,
    ⟨4, 6, [], [3], [7, 8], 1, 7⟩,
    ⟨4, 7, [], [3], [6], 1, 8⟩,
    ⟨4, 9, [], [3], [8], 1, 8⟩,
    ⟨5, 7, [], [3, 4], [6], 1, 7⟩,
    ⟨5, 9, [], [3, 4], [8], 1, 7⟩,
    ⟨6, 7, [[3, 4, 5]], [], [8], 1, 6⟩,
    ⟨6, 9, [[3, 4, 5]], [], [8], 1, 6⟩,
    ⟨7, 9, [], [6], [8], 1, 8⟩]
  required := []
  closure := []
  bad := ⟨none, {(1, 0), (4, 2), (0, 3), (7, 3), (9, 3)}⟩


private def k11t8p9_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, true, false, true, true, false, true, false, true],
    #[true, false, true, true, false, true, true, false, true, false, true],
    #[true, true, false, true, false, true, true, false, true, false, true],
    #[true, true, true, false, true, true, true, false, true, false, true],
    #[false, false, false, true, false, true, false, false, false, false, false],
    #[true, true, true, true, true, false, true, false, true, false, true],
    #[true, true, true, true, false, true, false, true, true, false, true],
    #[false, false, false, false, false, false, true, false, true, false, false],
    #[true, true, true, true, false, true, true, true, false, true, true],
    #[false, false, false, false, false, false, false, false, true, false, true],
    #[true, true, true, true, false, true, true, false, true, true, false]]

private theorem k11t8p9_adjacency_row_0 : ∀ j : Fin 11,
    k11t8p9.graph.Adj 0 j ↔ adjacencyTableLookup k11t8p9_adjacencyTable 0 j.val = true := by decide

private theorem k11t8p9_adjacency_row_1 : ∀ j : Fin 11,
    k11t8p9.graph.Adj 1 j ↔ adjacencyTableLookup k11t8p9_adjacencyTable 1 j.val = true := by decide

private theorem k11t8p9_adjacency_row_2 : ∀ j : Fin 11,
    k11t8p9.graph.Adj 2 j ↔ adjacencyTableLookup k11t8p9_adjacencyTable 2 j.val = true := by decide

private theorem k11t8p9_adjacency_row_3 : ∀ j : Fin 11,
    k11t8p9.graph.Adj 3 j ↔ adjacencyTableLookup k11t8p9_adjacencyTable 3 j.val = true := by decide

private theorem k11t8p9_adjacency_row_4 : ∀ j : Fin 11,
    k11t8p9.graph.Adj 4 j ↔ adjacencyTableLookup k11t8p9_adjacencyTable 4 j.val = true := by decide

private theorem k11t8p9_adjacency_row_5 : ∀ j : Fin 11,
    k11t8p9.graph.Adj 5 j ↔ adjacencyTableLookup k11t8p9_adjacencyTable 5 j.val = true := by decide

private theorem k11t8p9_adjacency_row_6 : ∀ j : Fin 11,
    k11t8p9.graph.Adj 6 j ↔ adjacencyTableLookup k11t8p9_adjacencyTable 6 j.val = true := by decide

private theorem k11t8p9_adjacency_row_7 : ∀ j : Fin 11,
    k11t8p9.graph.Adj 7 j ↔ adjacencyTableLookup k11t8p9_adjacencyTable 7 j.val = true := by decide

private theorem k11t8p9_adjacency_row_8 : ∀ j : Fin 11,
    k11t8p9.graph.Adj 8 j ↔ adjacencyTableLookup k11t8p9_adjacencyTable 8 j.val = true := by decide

private theorem k11t8p9_adjacency_row_9 : ∀ j : Fin 11,
    k11t8p9.graph.Adj 9 j ↔ adjacencyTableLookup k11t8p9_adjacencyTable 9 j.val = true := by decide

private theorem k11t8p9_adjacency_row_10 : ∀ j : Fin 11,
    k11t8p9.graph.Adj 10 j ↔ adjacencyTableLookup k11t8p9_adjacencyTable 10 j.val = true := by decide

private theorem k11t8p9_adjacency_eq : ∀ i j : Fin 11,
    k11t8p9.graph.Adj i j ↔ adjacencyTableLookup k11t8p9_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t8p9_adjacency_row_0 j

  · exact k11t8p9_adjacency_row_1 j

  · exact k11t8p9_adjacency_row_2 j

  · exact k11t8p9_adjacency_row_3 j

  · exact k11t8p9_adjacency_row_4 j

  · exact k11t8p9_adjacency_row_5 j

  · exact k11t8p9_adjacency_row_6 j

  · exact k11t8p9_adjacency_row_7 j

  · exact k11t8p9_adjacency_row_8 j

  · exact k11t8p9_adjacency_row_9 j

  · exact k11t8p9_adjacency_row_10 j

private def k11t8p9_tableGraph : SimpleGraph (Fin 11) :=
  adjacencyTableGraph k11t8p9.graph k11t8p9_adjacencyTable k11t8p9_adjacency_eq

private instance k11t8p9_tableGraph_decidableAdj :
    DecidableRel k11t8p9_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t8p9_adjacencyTable i.val j.val = true))

private theorem k11t8p9_tableGraph_eq : k11t8p9_tableGraph = k11t8p9.graph :=
  adjacencyTableGraph_eq k11t8p9.graph k11t8p9_adjacencyTable k11t8p9_adjacency_eq

private def k11t8p9_state_0 : ForbiddenMatrix 11 :=
  fun i j => ((#[#[∅, Finset.Icc 1 7, {1, 2}, {1, 2, 3}, Finset.Icc 1 6, {1, 2, 3}, {1, 2, 3}, Finset.Icc 1 6, ∅, Finset.Icc 1 6, ∅],
    #[Finset.Icc 1 7, ∅, ∅, ∅, Finset.Icc 1 6, ∅, ∅, Finset.Icc 1 6, ∅, Finset.Icc 1 6, ∅],
    #[{1, 2}, ∅, ∅, ∅, Finset.Icc 1 6, ∅, ∅, Finset.Icc 1 6, ∅, Finset.Icc 1 6, ∅],
    #[{1, 2, 3}, ∅, ∅, ∅, Finset.Icc 1 6, ∅, ∅, Finset.Icc 1 7, ∅, Finset.Icc 1 7, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 7, Finset.Icc 1 8, ∅, Finset.Icc 1 8, ∅],
    #[{1, 2, 3}, ∅, ∅, ∅, Finset.Icc 1 6, ∅, ∅, Finset.Icc 1 7, ∅, Finset.Icc 1 7, ∅],
    #[{1, 2, 3}, ∅, ∅, ∅, Finset.Icc 1 7, ∅, ∅, Finset.Icc 1 6, ∅, Finset.Icc 1 6, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 7, Finset.Icc 1 8, Finset.Icc 1 7, Finset.Icc 1 6, ∅, ∅, Finset.Icc 1 8, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 7, Finset.Icc 1 8, Finset.Icc 1 7, Finset.Icc 1 6, Finset.Icc 1 8, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t8p9_decode_entry_0 : decode 12 252 = Finset.Icc 2 7 := by decide

private theorem k11t8p9_decode_entry_1 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p9_decode_entry_2 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p9_decode_entry_3 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p9_decode_entry_4 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_5 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p9_decode_entry_6 : decode 12 14 = Finset.Icc 1 3 := by decide

private theorem k11t8p9_decode_entry_7 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_8 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_9 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_10 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_11 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_12 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_13 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_14 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_15 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_16 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p9_decode_entry_17 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p9_decode_entry_18 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_19 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p9_decode_entry_20 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p9_decode_entry_21 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p9_decode_entry_22 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p9_decode_entry_23 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p9_decode_entry_24 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_25 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p9_decode_entry_26 : decode 12 510 = Finset.Icc 1 8 := by decide

private def k11t8p9_mask_entries_0 : List (TemplateData (Fin 11) × ℕ) := [(⟨0, 1, [[3, 4, 5]], [], [], 2, 7⟩, 252), (⟨0, 1, [[3, 4, 5], [6, 7, 8, 9, 10]], [], [], 1, 2⟩, 6), (⟨0, 2, [[3, 4, 5], [6, 7, 8, 9, 10]], [], [], 1, 2⟩, 6), (⟨0, 3, [[6, 7, 8, 9, 10]], [], [4, 5], 1, 3⟩, 14), (⟨0, 4, [[6, 7, 8]], [], [3], 1, 6⟩, 126), (⟨0, 5, [[6, 7, 8, 9, 10]], [], [4, 3], 1, 3⟩, 14), (⟨0, 6, [[3, 4, 5]], [], [7, 8, 9, 10], 1, 3⟩, 14), (⟨0, 7, [[3, 4, 5]], [], [6], 1, 6⟩, 126), (⟨0, 9, [[3, 4, 5]], [], [8], 1, 6⟩, 126), (⟨1, 4, [[6, 7, 8]], [], [3], 1, 6⟩, 126), (⟨1, 7, [[3, 4, 5]], [], [6], 1, 6⟩, 126), (⟨1, 9, [[3, 4, 5]], [], [8], 1, 6⟩, 126), (⟨2, 4, [[6, 7, 8]], [], [3], 1, 6⟩, 126), (⟨2, 7, [[3, 4, 5]], [], [6], 1, 6⟩, 126), (⟨2, 9, [[3, 4, 5]], [], [8], 1, 6⟩, 126), (⟨3, 4, [[6, 7, 8]], [], [5], 1, 6⟩, 126), (⟨3, 7, [], [5, 4], [6], 1, 7⟩, 254), (⟨3, 9, [], [5, 4], [8], 1, 7⟩, 254), (⟨4, 5, [[6, 7, 8]], [3], [], 1, 6⟩, 126), (⟨4, 6, [], [3], [7, 8], 1, 7⟩, 254), (⟨4, 7, [], [3], [6], 1, 8⟩, 510), (⟨4, 9, [], [3], [8], 1, 8⟩, 510), (⟨5, 7, [], [3, 4], [6], 1, 7⟩, 254), (⟨5, 9, [], [3, 4], [8], 1, 7⟩, 254), (⟨6, 7, [[3, 4, 5]], [], [8], 1, 6⟩, 126), (⟨6, 9, [[3, 4, 5]], [], [8], 1, 6⟩, 126), (⟨7, 9, [], [6], [8], 1, 8⟩, 510)]

private theorem k11t8p9_decode_entries_0 : ∀ Tb ∈ k11t8p9_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t8p9_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p9_decode_entry_0, k11t8p9_decode_entry_1, k11t8p9_decode_entry_2, k11t8p9_decode_entry_3, k11t8p9_decode_entry_4, k11t8p9_decode_entry_5, k11t8p9_decode_entry_6, k11t8p9_decode_entry_7, k11t8p9_decode_entry_8, k11t8p9_decode_entry_9, k11t8p9_decode_entry_10, k11t8p9_decode_entry_11, k11t8p9_decode_entry_12, k11t8p9_decode_entry_13, k11t8p9_decode_entry_14, k11t8p9_decode_entry_15, k11t8p9_decode_entry_16, k11t8p9_decode_entry_17, k11t8p9_decode_entry_18, k11t8p9_decode_entry_19, k11t8p9_decode_entry_20, k11t8p9_decode_entry_21, k11t8p9_decode_entry_22, k11t8p9_decode_entry_23, k11t8p9_decode_entry_24, k11t8p9_decode_entry_25, k11t8p9_decode_entry_26⟩

private def k11t8p9_mask_block_0 : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 254, 6, 14, 126, 14, 14, 126, 0, 126, 0],
    #[254, 0, 0, 0, 126, 0, 0, 126, 0, 126, 0],
    #[6, 0, 0, 0, 126, 0, 0, 126, 0, 126, 0],
    #[14, 0, 0, 0, 126, 0, 0, 254, 0, 254, 0],
    #[126, 126, 126, 126, 0, 126, 254, 510, 0, 510, 0],
    #[14, 0, 0, 0, 126, 0, 0, 254, 0, 254, 0],
    #[14, 0, 0, 0, 254, 0, 0, 126, 0, 126, 0],
    #[126, 126, 126, 254, 510, 254, 126, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[126, 126, 126, 254, 510, 254, 126, 510, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p9_mask_block_0_eq_row_0 : ∀ j : Fin 11, (templateMaskMatrix k11t8p9_mask_entries_0) 0 j = k11t8p9_mask_block_0 0 j := by decide

private theorem k11t8p9_mask_block_0_eq_row_1 : ∀ j : Fin 11, (templateMaskMatrix k11t8p9_mask_entries_0) 1 j = k11t8p9_mask_block_0 1 j := by decide

private theorem k11t8p9_mask_block_0_eq_row_2 : ∀ j : Fin 11, (templateMaskMatrix k11t8p9_mask_entries_0) 2 j = k11t8p9_mask_block_0 2 j := by decide

private theorem k11t8p9_mask_block_0_eq_row_3 : ∀ j : Fin 11, (templateMaskMatrix k11t8p9_mask_entries_0) 3 j = k11t8p9_mask_block_0 3 j := by decide

private theorem k11t8p9_mask_block_0_eq_row_4 : ∀ j : Fin 11, (templateMaskMatrix k11t8p9_mask_entries_0) 4 j = k11t8p9_mask_block_0 4 j := by decide

private theorem k11t8p9_mask_block_0_eq_row_5 : ∀ j : Fin 11, (templateMaskMatrix k11t8p9_mask_entries_0) 5 j = k11t8p9_mask_block_0 5 j := by decide

private theorem k11t8p9_mask_block_0_eq_row_6 : ∀ j : Fin 11, (templateMaskMatrix k11t8p9_mask_entries_0) 6 j = k11t8p9_mask_block_0 6 j := by decide

private theorem k11t8p9_mask_block_0_eq_row_7 : ∀ j : Fin 11, (templateMaskMatrix k11t8p9_mask_entries_0) 7 j = k11t8p9_mask_block_0 7 j := by decide

private theorem k11t8p9_mask_block_0_eq_row_8 : ∀ j : Fin 11, (templateMaskMatrix k11t8p9_mask_entries_0) 8 j = k11t8p9_mask_block_0 8 j := by decide

private theorem k11t8p9_mask_block_0_eq_row_9 : ∀ j : Fin 11, (templateMaskMatrix k11t8p9_mask_entries_0) 9 j = k11t8p9_mask_block_0 9 j := by decide

private theorem k11t8p9_mask_block_0_eq_row_10 : ∀ j : Fin 11, (templateMaskMatrix k11t8p9_mask_entries_0) 10 j = k11t8p9_mask_block_0 10 j := by decide

private theorem k11t8p9_mask_block_0_eq : (templateMaskMatrix k11t8p9_mask_entries_0) = k11t8p9_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t8p9_mask_block_0_eq_row_0 j

  · exact k11t8p9_mask_block_0_eq_row_1 j

  · exact k11t8p9_mask_block_0_eq_row_2 j

  · exact k11t8p9_mask_block_0_eq_row_3 j

  · exact k11t8p9_mask_block_0_eq_row_4 j

  · exact k11t8p9_mask_block_0_eq_row_5 j

  · exact k11t8p9_mask_block_0_eq_row_6 j

  · exact k11t8p9_mask_block_0_eq_row_7 j

  · exact k11t8p9_mask_block_0_eq_row_8 j

  · exact k11t8p9_mask_block_0_eq_row_9 j

  · exact k11t8p9_mask_block_0_eq_row_10 j

private def k11t8p9_mask_entries : List (TemplateData (Fin 11) × ℕ) := k11t8p9_mask_entries_0

private theorem k11t8p9_decode_entries : ∀ Tb ∈ k11t8p9_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t8p9_decode_entries_0

private theorem k11t8p9_mask_entries_map : k11t8p9_mask_entries.map Prod.fst = k11t8p9.templates := by rfl

private def k11t8p9_template_mask : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 254, 6, 14, 126, 14, 14, 126, 0, 126, 0],
    #[254, 0, 0, 0, 126, 0, 0, 126, 0, 126, 0],
    #[6, 0, 0, 0, 126, 0, 0, 126, 0, 126, 0],
    #[14, 0, 0, 0, 126, 0, 0, 254, 0, 254, 0],
    #[126, 126, 126, 126, 0, 126, 254, 510, 0, 510, 0],
    #[14, 0, 0, 0, 126, 0, 0, 254, 0, 254, 0],
    #[14, 0, 0, 0, 254, 0, 0, 126, 0, 126, 0],
    #[126, 126, 126, 254, 510, 254, 126, 0, 0, 510, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[126, 126, 126, 254, 510, 254, 126, 510, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p9_mask_merged_eq_row_0 : ∀ j : Fin 11, (fun i j => k11t8p9_mask_block_0 i j) 0 j = k11t8p9_template_mask 0 j := by decide

private theorem k11t8p9_mask_merged_eq_row_1 : ∀ j : Fin 11, (fun i j => k11t8p9_mask_block_0 i j) 1 j = k11t8p9_template_mask 1 j := by decide

private theorem k11t8p9_mask_merged_eq_row_2 : ∀ j : Fin 11, (fun i j => k11t8p9_mask_block_0 i j) 2 j = k11t8p9_template_mask 2 j := by decide

private theorem k11t8p9_mask_merged_eq_row_3 : ∀ j : Fin 11, (fun i j => k11t8p9_mask_block_0 i j) 3 j = k11t8p9_template_mask 3 j := by decide

private theorem k11t8p9_mask_merged_eq_row_4 : ∀ j : Fin 11, (fun i j => k11t8p9_mask_block_0 i j) 4 j = k11t8p9_template_mask 4 j := by decide

private theorem k11t8p9_mask_merged_eq_row_5 : ∀ j : Fin 11, (fun i j => k11t8p9_mask_block_0 i j) 5 j = k11t8p9_template_mask 5 j := by decide

private theorem k11t8p9_mask_merged_eq_row_6 : ∀ j : Fin 11, (fun i j => k11t8p9_mask_block_0 i j) 6 j = k11t8p9_template_mask 6 j := by decide

private theorem k11t8p9_mask_merged_eq_row_7 : ∀ j : Fin 11, (fun i j => k11t8p9_mask_block_0 i j) 7 j = k11t8p9_template_mask 7 j := by decide

private theorem k11t8p9_mask_merged_eq_row_8 : ∀ j : Fin 11, (fun i j => k11t8p9_mask_block_0 i j) 8 j = k11t8p9_template_mask 8 j := by decide

private theorem k11t8p9_mask_merged_eq_row_9 : ∀ j : Fin 11, (fun i j => k11t8p9_mask_block_0 i j) 9 j = k11t8p9_template_mask 9 j := by decide

private theorem k11t8p9_mask_merged_eq_row_10 : ∀ j : Fin 11, (fun i j => k11t8p9_mask_block_0 i j) 10 j = k11t8p9_template_mask 10 j := by decide

private theorem k11t8p9_mask_merged_eq : (fun i j => k11t8p9_mask_block_0 i j) = k11t8p9_template_mask := by
  funext i j
  fin_cases i

  · exact k11t8p9_mask_merged_eq_row_0 j

  · exact k11t8p9_mask_merged_eq_row_1 j

  · exact k11t8p9_mask_merged_eq_row_2 j

  · exact k11t8p9_mask_merged_eq_row_3 j

  · exact k11t8p9_mask_merged_eq_row_4 j

  · exact k11t8p9_mask_merged_eq_row_5 j

  · exact k11t8p9_mask_merged_eq_row_6 j

  · exact k11t8p9_mask_merged_eq_row_7 j

  · exact k11t8p9_mask_merged_eq_row_8 j

  · exact k11t8p9_mask_merged_eq_row_9 j

  · exact k11t8p9_mask_merged_eq_row_10 j

private theorem k11t8p9_template_mask_eq : templateMaskMatrix k11t8p9_mask_entries = k11t8p9_template_mask := by
  funext i j
  change templateMaskMatrix (k11t8p9_mask_entries_0) i j = _
  simp only [k11t8p9_mask_block_0_eq]
  exact congrFun (congrFun k11t8p9_mask_merged_eq i) j

private theorem k11t8p9_initial_decoded_eq_row_0 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) 0 j = k11t8p9_state_0 0 j := by decide

private theorem k11t8p9_initial_decoded_eq_row_1 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) 1 j = k11t8p9_state_0 1 j := by decide

private theorem k11t8p9_initial_decoded_eq_row_2 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) 2 j = k11t8p9_state_0 2 j := by decide

private theorem k11t8p9_initial_decoded_eq_row_3 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) 3 j = k11t8p9_state_0 3 j := by decide

private theorem k11t8p9_initial_decoded_eq_row_4 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) 4 j = k11t8p9_state_0 4 j := by decide

private theorem k11t8p9_initial_decoded_eq_row_5 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) 5 j = k11t8p9_state_0 5 j := by decide

private theorem k11t8p9_initial_decoded_eq_row_6 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) 6 j = k11t8p9_state_0 6 j := by decide

private theorem k11t8p9_initial_decoded_eq_row_7 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) 7 j = k11t8p9_state_0 7 j := by decide

private theorem k11t8p9_initial_decoded_eq_row_8 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) 8 j = k11t8p9_state_0 8 j := by decide

private theorem k11t8p9_initial_decoded_eq_row_9 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) 9 j = k11t8p9_state_0 9 j := by decide

private theorem k11t8p9_initial_decoded_eq_row_10 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) 10 j = k11t8p9_state_0 10 j := by decide

private theorem k11t8p9_initial_decoded_eq : (fun i j => decode 12 (k11t8p9_template_mask i j) ∪ requiredMatrix 11 k11t8p9.required i j) = k11t8p9_state_0 := by
  funext i j
  fin_cases i

  · exact k11t8p9_initial_decoded_eq_row_0 j

  · exact k11t8p9_initial_decoded_eq_row_1 j

  · exact k11t8p9_initial_decoded_eq_row_2 j

  · exact k11t8p9_initial_decoded_eq_row_3 j

  · exact k11t8p9_initial_decoded_eq_row_4 j

  · exact k11t8p9_initial_decoded_eq_row_5 j

  · exact k11t8p9_initial_decoded_eq_row_6 j

  · exact k11t8p9_initial_decoded_eq_row_7 j

  · exact k11t8p9_initial_decoded_eq_row_8 j

  · exact k11t8p9_initial_decoded_eq_row_9 j

  · exact k11t8p9_initial_decoded_eq_row_10 j

private theorem k11t8p9_initial_eq : k11t8p9.initialMatrix 11 = k11t8p9_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t8p9_mask_entries k11t8p9_decode_entries
  rw [k11t8p9_mask_entries_map, k11t8p9_template_mask_eq] at h
  funext i j
  change templateMatrix k11t8p9.templates i j ∪ requiredMatrix 11 k11t8p9.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t8p9_initial_decoded_eq i) j

private theorem k11t8p9_closure_0 : ClosureCheck k11t8p9.graph k11t8p9_state_0 11 8 [] := by trivial

private theorem k11t8p9_matrix_eq : k11t8p9.matrix 11 = k11t8p9_state_0 := by
  change closureMatrix (k11t8p9.initialMatrix 11) _ = _
  rw [k11t8p9_initial_eq]
  change closureMatrix k11t8p9_state_0 [] = _
  rfl

private theorem k11t8p9_part_0 : k11t8p9.chains.flatten = List.finRange _ := by decide

private theorem k11t8p9_part_1 : k11t8p9.chains.map List.length = ([[], [], [], [1], [1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t8p9_part_2 : k11t8p9.chains.map (fun l => l.map (fun i => decide (i ∈ k11t8p9.clique))) = ([[], [], [], [1], [1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k11t8p9_templates_item_0 : (⟨0, 1, [[3, 4, 5]], [], [], 2, 7⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_1 : (⟨0, 1, [[3, 4, 5], [6, 7, 8, 9, 10]], [], [], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_2 : (⟨0, 2, [[3, 4, 5], [6, 7, 8, 9, 10]], [], [], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_3 : (⟨0, 3, [[6, 7, 8, 9, 10]], [], [4, 5], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_4 : (⟨0, 4, [[6, 7, 8]], [], [3], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_5 : (⟨0, 5, [[6, 7, 8, 9, 10]], [], [4, 3], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_6 : (⟨0, 6, [[3, 4, 5]], [], [7, 8, 9, 10], 1, 3⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_7 : (⟨0, 7, [[3, 4, 5]], [], [6], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_8 : (⟨0, 9, [[3, 4, 5]], [], [8], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_9 : (⟨1, 4, [[6, 7, 8]], [], [3], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_10 : (⟨1, 7, [[3, 4, 5]], [], [6], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_11 : (⟨1, 9, [[3, 4, 5]], [], [8], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_12 : (⟨2, 4, [[6, 7, 8]], [], [3], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_13 : (⟨2, 7, [[3, 4, 5]], [], [6], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_14 : (⟨2, 9, [[3, 4, 5]], [], [8], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_15 : (⟨3, 4, [[6, 7, 8]], [], [5], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_16 : (⟨3, 7, [], [5, 4], [6], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_17 : (⟨3, 9, [], [5, 4], [8], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_18 : (⟨4, 5, [[6, 7, 8]], [3], [], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_19 : (⟨4, 6, [], [3], [7, 8], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_20 : (⟨4, 7, [], [3], [6], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_21 : (⟨4, 9, [], [3], [8], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_22 : (⟨5, 7, [], [3, 4], [6], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_23 : (⟨5, 9, [], [3, 4], [8], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_24 : (⟨6, 7, [[3, 4, 5]], [], [8], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_25 : (⟨6, 9, [[3, 4, 5]], [], [8], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_item_26 : (⟨7, 9, [], [6], [8], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p9_tableGraph_eq]
  decide

private theorem k11t8p9_templates_fast_block_0_check : ∀ T ∈ k11t8p9_mask_entries_0.map Prod.fst, T.Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t8p9_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p9_templates_item_0, k11t8p9_templates_item_1, k11t8p9_templates_item_2, k11t8p9_templates_item_3, k11t8p9_templates_item_4, k11t8p9_templates_item_5, k11t8p9_templates_item_6, k11t8p9_templates_item_7, k11t8p9_templates_item_8, k11t8p9_templates_item_9, k11t8p9_templates_item_10, k11t8p9_templates_item_11, k11t8p9_templates_item_12, k11t8p9_templates_item_13, k11t8p9_templates_item_14, k11t8p9_templates_item_15, k11t8p9_templates_item_16, k11t8p9_templates_item_17, k11t8p9_templates_item_18, k11t8p9_templates_item_19, k11t8p9_templates_item_20, k11t8p9_templates_item_21, k11t8p9_templates_item_22, k11t8p9_templates_item_23, k11t8p9_templates_item_24, k11t8p9_templates_item_25, k11t8p9_templates_item_26⟩

private theorem k11t8p9_part_3 : ∀ T ∈ k11t8p9.templates, T.Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t8p9_mask_entries_0.map Prod.fst), T.Check k11t8p9.graph k11t8p9.clique 11 (patternAmount ([[], [], [], [1], [1, 1]] : List (List ℕ))) (([[], [], [], [1], [1, 1]] : List (List ℕ)).map List.length).sum
  exact k11t8p9_templates_fast_block_0_check

private theorem k11t8p9_part_4 : ∀ p ∈ k11t8p9.required, p.Check k11t8p9.graph 11 := by decide

private theorem k11t8p9_part_5 : ClosureCheck k11t8p9.graph (k11t8p9.initialMatrix 11) 11 8 k11t8p9.closure := by
  rw [k11t8p9_initial_eq]
  exact k11t8p9_closure_0

private theorem k11t8p9_part_6 : k11t8p9.bad.Check k11t8p9.graph (k11t8p9.matrix 11) 11 8 := by
  rw [k11t8p9_matrix_eq]
  decide

theorem k11t8p9_check : k11t8p9.Check 11 8 [[], [], [], [1], [1, 1]] :=
  ⟨k11t8p9_part_0, k11t8p9_part_1, k11t8p9_part_2, k11t8p9_part_3, k11t8p9_part_4, k11t8p9_part_5, k11t8p9_part_6⟩
def k11t8p10 : LayoutCertificate 11 where
  chains := [[0], [1], [2, 3, 4], [5, 6, 7], [8, 9, 10]]
  clique := {0, 1, 2, 4, 5, 7, 8, 10}
  templates := [⟨0, 1, [[2, 3, 4]], [], [], 2, 7⟩,
    ⟨0, 1, [[2, 3, 4], [5, 6, 7], [8, 9, 10]], [], [], 1, 1⟩,
    ⟨0, 2, [[5, 6, 7], [8, 9, 10]], [], [3, 4], 1, 2⟩,
    ⟨0, 3, [[5, 6, 7]], [], [2], 1, 6⟩,
    ⟨0, 4, [[5, 6, 7], [8, 9, 10]], [], [3, 2], 1, 2⟩,
    ⟨0, 5, [[2, 3, 4], [8, 9, 10]], [], [6, 7], 1, 2⟩,
    ⟨0, 6, [[2, 3, 4]], [], [5], 1, 6⟩,
    ⟨0, 7, [[2, 3, 4], [8, 9, 10]], [], [6, 5], 1, 2⟩,
    ⟨0, 8, [[2, 3, 4], [5, 6, 7]], [], [9, 10], 1, 2⟩,
    ⟨1, 2, [], [], [3, 4], 2, 8⟩,
    ⟨1, 2, [[5, 6, 7], [8, 9, 10]], [], [3, 4], 1, 2⟩,
    ⟨1, 3, [[5, 6, 7]], [], [2], 1, 6⟩,
    ⟨1, 4, [[5, 6, 7], [8, 9, 10]], [], [3, 2], 1, 2⟩,
    ⟨1, 5, [[2, 3, 4], [8, 9, 10]], [], [6, 7], 1, 2⟩,
    ⟨1, 6, [[2, 3, 4]], [], [5], 1, 6⟩,
    ⟨1, 7, [[2, 3, 4], [8, 9, 10]], [], [6, 5], 1, 2⟩,
    ⟨1, 8, [[2, 3, 4], [5, 6, 7]], [], [9, 10], 1, 2⟩,
    ⟨2, 3, [[5, 6, 7]], [], [4], 1, 6⟩,
    ⟨2, 6, [], [4, 3], [5], 1, 7⟩,
    ⟨3, 4, [[5, 6, 7]], [2], [], 1, 6⟩,
    ⟨3, 5, [], [2], [6, 7], 1, 7⟩,
    ⟨3, 6, [], [2], [5], 1, 8⟩,
    ⟨3, 7, [], [2], [6, 5], 1, 7⟩,
    ⟨3, 8, [[5, 6, 7]], [2], [], 1, 6⟩,
    ⟨4, 6, [], [2, 3], [5], 1, 7⟩,
    ⟨5, 6, [[2, 3, 4]], [], [7], 1, 6⟩,
    ⟨6, 7, [[2, 3, 4]], [5], [], 1, 6⟩,
    ⟨6, 8, [[2, 3, 4]], [5], [], 1, 6⟩]
  required := []
  closure := []
  bad := ⟨none, {(2, 0), (0, 2), (3, 3), (6, 3), (1, 3)}⟩


private def k11t8p10_adjacencyTable : Array (Array Bool) :=
  #[#[false, true, true, false, true, true, false, true, true, false, true],
    #[true, false, true, false, true, true, false, true, true, false, true],
    #[true, true, false, true, true, true, false, true, true, false, true],
    #[false, false, true, false, true, false, false, false, false, false, false],
    #[true, true, true, true, false, true, false, true, true, false, true],
    #[true, true, true, false, true, false, true, true, true, false, true],
    #[false, false, false, false, false, true, false, true, false, false, false],
    #[true, true, true, false, true, true, true, false, true, false, true],
    #[true, true, true, false, true, true, false, true, false, true, true],
    #[false, false, false, false, false, false, false, false, true, false, true],
    #[true, true, true, false, true, true, false, true, true, true, false]]

private theorem k11t8p10_adjacency_row_0 : ∀ j : Fin 11,
    k11t8p10.graph.Adj 0 j ↔ adjacencyTableLookup k11t8p10_adjacencyTable 0 j.val = true := by decide

private theorem k11t8p10_adjacency_row_1 : ∀ j : Fin 11,
    k11t8p10.graph.Adj 1 j ↔ adjacencyTableLookup k11t8p10_adjacencyTable 1 j.val = true := by decide

private theorem k11t8p10_adjacency_row_2 : ∀ j : Fin 11,
    k11t8p10.graph.Adj 2 j ↔ adjacencyTableLookup k11t8p10_adjacencyTable 2 j.val = true := by decide

private theorem k11t8p10_adjacency_row_3 : ∀ j : Fin 11,
    k11t8p10.graph.Adj 3 j ↔ adjacencyTableLookup k11t8p10_adjacencyTable 3 j.val = true := by decide

private theorem k11t8p10_adjacency_row_4 : ∀ j : Fin 11,
    k11t8p10.graph.Adj 4 j ↔ adjacencyTableLookup k11t8p10_adjacencyTable 4 j.val = true := by decide

private theorem k11t8p10_adjacency_row_5 : ∀ j : Fin 11,
    k11t8p10.graph.Adj 5 j ↔ adjacencyTableLookup k11t8p10_adjacencyTable 5 j.val = true := by decide

private theorem k11t8p10_adjacency_row_6 : ∀ j : Fin 11,
    k11t8p10.graph.Adj 6 j ↔ adjacencyTableLookup k11t8p10_adjacencyTable 6 j.val = true := by decide

private theorem k11t8p10_adjacency_row_7 : ∀ j : Fin 11,
    k11t8p10.graph.Adj 7 j ↔ adjacencyTableLookup k11t8p10_adjacencyTable 7 j.val = true := by decide

private theorem k11t8p10_adjacency_row_8 : ∀ j : Fin 11,
    k11t8p10.graph.Adj 8 j ↔ adjacencyTableLookup k11t8p10_adjacencyTable 8 j.val = true := by decide

private theorem k11t8p10_adjacency_row_9 : ∀ j : Fin 11,
    k11t8p10.graph.Adj 9 j ↔ adjacencyTableLookup k11t8p10_adjacencyTable 9 j.val = true := by decide

private theorem k11t8p10_adjacency_row_10 : ∀ j : Fin 11,
    k11t8p10.graph.Adj 10 j ↔ adjacencyTableLookup k11t8p10_adjacencyTable 10 j.val = true := by decide

private theorem k11t8p10_adjacency_eq : ∀ i j : Fin 11,
    k11t8p10.graph.Adj i j ↔ adjacencyTableLookup k11t8p10_adjacencyTable i.val j.val = true := by
  intro i j
  fin_cases i

  · exact k11t8p10_adjacency_row_0 j

  · exact k11t8p10_adjacency_row_1 j

  · exact k11t8p10_adjacency_row_2 j

  · exact k11t8p10_adjacency_row_3 j

  · exact k11t8p10_adjacency_row_4 j

  · exact k11t8p10_adjacency_row_5 j

  · exact k11t8p10_adjacency_row_6 j

  · exact k11t8p10_adjacency_row_7 j

  · exact k11t8p10_adjacency_row_8 j

  · exact k11t8p10_adjacency_row_9 j

  · exact k11t8p10_adjacency_row_10 j

private def k11t8p10_tableGraph : SimpleGraph (Fin 11) :=
  adjacencyTableGraph k11t8p10.graph k11t8p10_adjacencyTable k11t8p10_adjacency_eq

private instance k11t8p10_tableGraph_decidableAdj :
    DecidableRel k11t8p10_tableGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup k11t8p10_adjacencyTable i.val j.val = true))

private theorem k11t8p10_tableGraph_eq : k11t8p10_tableGraph = k11t8p10.graph :=
  adjacencyTableGraph_eq k11t8p10.graph k11t8p10_adjacencyTable k11t8p10_adjacency_eq

private def k11t8p10_state_0 : ForbiddenMatrix 11 :=
  fun i j => ((#[#[∅, Finset.Icc 1 7, {1, 2}, Finset.Icc 1 6, {1, 2}, {1, 2}, Finset.Icc 1 6, {1, 2}, {1, 2}, ∅, ∅],
    #[Finset.Icc 1 7, ∅, Finset.Icc 1 8, Finset.Icc 1 6, {1, 2}, {1, 2}, Finset.Icc 1 6, {1, 2}, {1, 2}, ∅, ∅],
    #[{1, 2}, Finset.Icc 1 8, ∅, Finset.Icc 1 6, ∅, ∅, Finset.Icc 1 7, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 7, Finset.Icc 1 8, Finset.Icc 1 7, Finset.Icc 1 6, ∅, ∅],
    #[{1, 2}, {1, 2}, ∅, Finset.Icc 1 6, ∅, ∅, Finset.Icc 1 7, ∅, ∅, ∅, ∅],
    #[{1, 2}, {1, 2}, ∅, Finset.Icc 1 7, ∅, ∅, Finset.Icc 1 6, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 7, Finset.Icc 1 8, Finset.Icc 1 7, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅],
    #[{1, 2}, {1, 2}, ∅, Finset.Icc 1 7, ∅, ∅, Finset.Icc 1 6, ∅, ∅, ∅, ∅],
    #[{1, 2}, {1, 2}, ∅, Finset.Icc 1 6, ∅, ∅, Finset.Icc 1 6, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k11t8p10_decode_entry_0 : decode 12 252 = Finset.Icc 2 7 := by decide

private theorem k11t8p10_decode_entry_1 : decode 12 2 = Finset.Icc 1 1 := by decide

private theorem k11t8p10_decode_entry_2 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p10_decode_entry_3 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p10_decode_entry_4 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p10_decode_entry_5 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p10_decode_entry_6 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p10_decode_entry_7 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p10_decode_entry_8 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p10_decode_entry_9 : decode 12 508 = Finset.Icc 2 8 := by decide

private theorem k11t8p10_decode_entry_10 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p10_decode_entry_11 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p10_decode_entry_12 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p10_decode_entry_13 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p10_decode_entry_14 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p10_decode_entry_15 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p10_decode_entry_16 : decode 12 6 = Finset.Icc 1 2 := by decide

private theorem k11t8p10_decode_entry_17 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p10_decode_entry_18 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p10_decode_entry_19 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p10_decode_entry_20 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p10_decode_entry_21 : decode 12 510 = Finset.Icc 1 8 := by decide

private theorem k11t8p10_decode_entry_22 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p10_decode_entry_23 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p10_decode_entry_24 : decode 12 254 = Finset.Icc 1 7 := by decide

private theorem k11t8p10_decode_entry_25 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p10_decode_entry_26 : decode 12 126 = Finset.Icc 1 6 := by decide

private theorem k11t8p10_decode_entry_27 : decode 12 126 = Finset.Icc 1 6 := by decide

private def k11t8p10_mask_entries_0 : List (TemplateData (Fin 11) × ℕ) := [(⟨0, 1, [[2, 3, 4]], [], [], 2, 7⟩, 252), (⟨0, 1, [[2, 3, 4], [5, 6, 7], [8, 9, 10]], [], [], 1, 1⟩, 2), (⟨0, 2, [[5, 6, 7], [8, 9, 10]], [], [3, 4], 1, 2⟩, 6), (⟨0, 3, [[5, 6, 7]], [], [2], 1, 6⟩, 126), (⟨0, 4, [[5, 6, 7], [8, 9, 10]], [], [3, 2], 1, 2⟩, 6), (⟨0, 5, [[2, 3, 4], [8, 9, 10]], [], [6, 7], 1, 2⟩, 6), (⟨0, 6, [[2, 3, 4]], [], [5], 1, 6⟩, 126), (⟨0, 7, [[2, 3, 4], [8, 9, 10]], [], [6, 5], 1, 2⟩, 6), (⟨0, 8, [[2, 3, 4], [5, 6, 7]], [], [9, 10], 1, 2⟩, 6), (⟨1, 2, [], [], [3, 4], 2, 8⟩, 508), (⟨1, 2, [[5, 6, 7], [8, 9, 10]], [], [3, 4], 1, 2⟩, 6), (⟨1, 3, [[5, 6, 7]], [], [2], 1, 6⟩, 126), (⟨1, 4, [[5, 6, 7], [8, 9, 10]], [], [3, 2], 1, 2⟩, 6), (⟨1, 5, [[2, 3, 4], [8, 9, 10]], [], [6, 7], 1, 2⟩, 6), (⟨1, 6, [[2, 3, 4]], [], [5], 1, 6⟩, 126), (⟨1, 7, [[2, 3, 4], [8, 9, 10]], [], [6, 5], 1, 2⟩, 6), (⟨1, 8, [[2, 3, 4], [5, 6, 7]], [], [9, 10], 1, 2⟩, 6), (⟨2, 3, [[5, 6, 7]], [], [4], 1, 6⟩, 126), (⟨2, 6, [], [4, 3], [5], 1, 7⟩, 254), (⟨3, 4, [[5, 6, 7]], [2], [], 1, 6⟩, 126), (⟨3, 5, [], [2], [6, 7], 1, 7⟩, 254), (⟨3, 6, [], [2], [5], 1, 8⟩, 510), (⟨3, 7, [], [2], [6, 5], 1, 7⟩, 254), (⟨3, 8, [[5, 6, 7]], [2], [], 1, 6⟩, 126), (⟨4, 6, [], [2, 3], [5], 1, 7⟩, 254), (⟨5, 6, [[2, 3, 4]], [], [7], 1, 6⟩, 126), (⟨6, 7, [[2, 3, 4]], [5], [], 1, 6⟩, 126), (⟨6, 8, [[2, 3, 4]], [5], [], 1, 6⟩, 126)]

private theorem k11t8p10_decode_entries_0 : ∀ Tb ∈ k11t8p10_mask_entries_0, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := by
  simp only [k11t8p10_mask_entries_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p10_decode_entry_0, k11t8p10_decode_entry_1, k11t8p10_decode_entry_2, k11t8p10_decode_entry_3, k11t8p10_decode_entry_4, k11t8p10_decode_entry_5, k11t8p10_decode_entry_6, k11t8p10_decode_entry_7, k11t8p10_decode_entry_8, k11t8p10_decode_entry_9, k11t8p10_decode_entry_10, k11t8p10_decode_entry_11, k11t8p10_decode_entry_12, k11t8p10_decode_entry_13, k11t8p10_decode_entry_14, k11t8p10_decode_entry_15, k11t8p10_decode_entry_16, k11t8p10_decode_entry_17, k11t8p10_decode_entry_18, k11t8p10_decode_entry_19, k11t8p10_decode_entry_20, k11t8p10_decode_entry_21, k11t8p10_decode_entry_22, k11t8p10_decode_entry_23, k11t8p10_decode_entry_24, k11t8p10_decode_entry_25, k11t8p10_decode_entry_26, k11t8p10_decode_entry_27⟩

private def k11t8p10_mask_block_0 : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 254, 6, 126, 6, 6, 126, 6, 6, 0, 0],
    #[254, 0, 510, 126, 6, 6, 126, 6, 6, 0, 0],
    #[6, 510, 0, 126, 0, 0, 254, 0, 0, 0, 0],
    #[126, 126, 126, 0, 126, 254, 510, 254, 126, 0, 0],
    #[6, 6, 0, 126, 0, 0, 254, 0, 0, 0, 0],
    #[6, 6, 0, 254, 0, 0, 126, 0, 0, 0, 0],
    #[126, 126, 254, 510, 254, 126, 0, 126, 126, 0, 0],
    #[6, 6, 0, 254, 0, 0, 126, 0, 0, 0, 0],
    #[6, 6, 0, 126, 0, 0, 126, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p10_mask_block_0_eq_row_0 : ∀ j : Fin 11, (templateMaskMatrix k11t8p10_mask_entries_0) 0 j = k11t8p10_mask_block_0 0 j := by decide

private theorem k11t8p10_mask_block_0_eq_row_1 : ∀ j : Fin 11, (templateMaskMatrix k11t8p10_mask_entries_0) 1 j = k11t8p10_mask_block_0 1 j := by decide

private theorem k11t8p10_mask_block_0_eq_row_2 : ∀ j : Fin 11, (templateMaskMatrix k11t8p10_mask_entries_0) 2 j = k11t8p10_mask_block_0 2 j := by decide

private theorem k11t8p10_mask_block_0_eq_row_3 : ∀ j : Fin 11, (templateMaskMatrix k11t8p10_mask_entries_0) 3 j = k11t8p10_mask_block_0 3 j := by decide

private theorem k11t8p10_mask_block_0_eq_row_4 : ∀ j : Fin 11, (templateMaskMatrix k11t8p10_mask_entries_0) 4 j = k11t8p10_mask_block_0 4 j := by decide

private theorem k11t8p10_mask_block_0_eq_row_5 : ∀ j : Fin 11, (templateMaskMatrix k11t8p10_mask_entries_0) 5 j = k11t8p10_mask_block_0 5 j := by decide

private theorem k11t8p10_mask_block_0_eq_row_6 : ∀ j : Fin 11, (templateMaskMatrix k11t8p10_mask_entries_0) 6 j = k11t8p10_mask_block_0 6 j := by decide

private theorem k11t8p10_mask_block_0_eq_row_7 : ∀ j : Fin 11, (templateMaskMatrix k11t8p10_mask_entries_0) 7 j = k11t8p10_mask_block_0 7 j := by decide

private theorem k11t8p10_mask_block_0_eq_row_8 : ∀ j : Fin 11, (templateMaskMatrix k11t8p10_mask_entries_0) 8 j = k11t8p10_mask_block_0 8 j := by decide

private theorem k11t8p10_mask_block_0_eq_row_9 : ∀ j : Fin 11, (templateMaskMatrix k11t8p10_mask_entries_0) 9 j = k11t8p10_mask_block_0 9 j := by decide

private theorem k11t8p10_mask_block_0_eq_row_10 : ∀ j : Fin 11, (templateMaskMatrix k11t8p10_mask_entries_0) 10 j = k11t8p10_mask_block_0 10 j := by decide

private theorem k11t8p10_mask_block_0_eq : (templateMaskMatrix k11t8p10_mask_entries_0) = k11t8p10_mask_block_0 := by
  funext i j
  fin_cases i

  · exact k11t8p10_mask_block_0_eq_row_0 j

  · exact k11t8p10_mask_block_0_eq_row_1 j

  · exact k11t8p10_mask_block_0_eq_row_2 j

  · exact k11t8p10_mask_block_0_eq_row_3 j

  · exact k11t8p10_mask_block_0_eq_row_4 j

  · exact k11t8p10_mask_block_0_eq_row_5 j

  · exact k11t8p10_mask_block_0_eq_row_6 j

  · exact k11t8p10_mask_block_0_eq_row_7 j

  · exact k11t8p10_mask_block_0_eq_row_8 j

  · exact k11t8p10_mask_block_0_eq_row_9 j

  · exact k11t8p10_mask_block_0_eq_row_10 j

private def k11t8p10_mask_entries : List (TemplateData (Fin 11) × ℕ) := k11t8p10_mask_entries_0

private theorem k11t8p10_decode_entries : ∀ Tb ∈ k11t8p10_mask_entries, decode 12 Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi := k11t8p10_decode_entries_0

private theorem k11t8p10_mask_entries_map : k11t8p10_mask_entries.map Prod.fst = k11t8p10.templates := by rfl

private def k11t8p10_template_mask : Fin 11 → Fin 11 → ℕ :=
  fun i j => ((#[#[0, 254, 6, 126, 6, 6, 126, 6, 6, 0, 0],
    #[254, 0, 510, 126, 6, 6, 126, 6, 6, 0, 0],
    #[6, 510, 0, 126, 0, 0, 254, 0, 0, 0, 0],
    #[126, 126, 126, 0, 126, 254, 510, 254, 126, 0, 0],
    #[6, 6, 0, 126, 0, 0, 254, 0, 0, 0, 0],
    #[6, 6, 0, 254, 0, 0, 126, 0, 0, 0, 0],
    #[126, 126, 254, 510, 254, 126, 0, 126, 126, 0, 0],
    #[6, 6, 0, 254, 0, 0, 126, 0, 0, 0, 0],
    #[6, 6, 0, 126, 0, 0, 126, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ)).getD i.val #[]).getD j.val 0

private theorem k11t8p10_mask_merged_eq_row_0 : ∀ j : Fin 11, (fun i j => k11t8p10_mask_block_0 i j) 0 j = k11t8p10_template_mask 0 j := by decide

private theorem k11t8p10_mask_merged_eq_row_1 : ∀ j : Fin 11, (fun i j => k11t8p10_mask_block_0 i j) 1 j = k11t8p10_template_mask 1 j := by decide

private theorem k11t8p10_mask_merged_eq_row_2 : ∀ j : Fin 11, (fun i j => k11t8p10_mask_block_0 i j) 2 j = k11t8p10_template_mask 2 j := by decide

private theorem k11t8p10_mask_merged_eq_row_3 : ∀ j : Fin 11, (fun i j => k11t8p10_mask_block_0 i j) 3 j = k11t8p10_template_mask 3 j := by decide

private theorem k11t8p10_mask_merged_eq_row_4 : ∀ j : Fin 11, (fun i j => k11t8p10_mask_block_0 i j) 4 j = k11t8p10_template_mask 4 j := by decide

private theorem k11t8p10_mask_merged_eq_row_5 : ∀ j : Fin 11, (fun i j => k11t8p10_mask_block_0 i j) 5 j = k11t8p10_template_mask 5 j := by decide

private theorem k11t8p10_mask_merged_eq_row_6 : ∀ j : Fin 11, (fun i j => k11t8p10_mask_block_0 i j) 6 j = k11t8p10_template_mask 6 j := by decide

private theorem k11t8p10_mask_merged_eq_row_7 : ∀ j : Fin 11, (fun i j => k11t8p10_mask_block_0 i j) 7 j = k11t8p10_template_mask 7 j := by decide

private theorem k11t8p10_mask_merged_eq_row_8 : ∀ j : Fin 11, (fun i j => k11t8p10_mask_block_0 i j) 8 j = k11t8p10_template_mask 8 j := by decide

private theorem k11t8p10_mask_merged_eq_row_9 : ∀ j : Fin 11, (fun i j => k11t8p10_mask_block_0 i j) 9 j = k11t8p10_template_mask 9 j := by decide

private theorem k11t8p10_mask_merged_eq_row_10 : ∀ j : Fin 11, (fun i j => k11t8p10_mask_block_0 i j) 10 j = k11t8p10_template_mask 10 j := by decide

private theorem k11t8p10_mask_merged_eq : (fun i j => k11t8p10_mask_block_0 i j) = k11t8p10_template_mask := by
  funext i j
  fin_cases i

  · exact k11t8p10_mask_merged_eq_row_0 j

  · exact k11t8p10_mask_merged_eq_row_1 j

  · exact k11t8p10_mask_merged_eq_row_2 j

  · exact k11t8p10_mask_merged_eq_row_3 j

  · exact k11t8p10_mask_merged_eq_row_4 j

  · exact k11t8p10_mask_merged_eq_row_5 j

  · exact k11t8p10_mask_merged_eq_row_6 j

  · exact k11t8p10_mask_merged_eq_row_7 j

  · exact k11t8p10_mask_merged_eq_row_8 j

  · exact k11t8p10_mask_merged_eq_row_9 j

  · exact k11t8p10_mask_merged_eq_row_10 j

private theorem k11t8p10_template_mask_eq : templateMaskMatrix k11t8p10_mask_entries = k11t8p10_template_mask := by
  funext i j
  change templateMaskMatrix (k11t8p10_mask_entries_0) i j = _
  simp only [k11t8p10_mask_block_0_eq]
  exact congrFun (congrFun k11t8p10_mask_merged_eq i) j

private theorem k11t8p10_initial_decoded_eq_row_0 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) 0 j = k11t8p10_state_0 0 j := by decide

private theorem k11t8p10_initial_decoded_eq_row_1 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) 1 j = k11t8p10_state_0 1 j := by decide

private theorem k11t8p10_initial_decoded_eq_row_2 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) 2 j = k11t8p10_state_0 2 j := by decide

private theorem k11t8p10_initial_decoded_eq_row_3 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) 3 j = k11t8p10_state_0 3 j := by decide

private theorem k11t8p10_initial_decoded_eq_row_4 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) 4 j = k11t8p10_state_0 4 j := by decide

private theorem k11t8p10_initial_decoded_eq_row_5 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) 5 j = k11t8p10_state_0 5 j := by decide

private theorem k11t8p10_initial_decoded_eq_row_6 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) 6 j = k11t8p10_state_0 6 j := by decide

private theorem k11t8p10_initial_decoded_eq_row_7 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) 7 j = k11t8p10_state_0 7 j := by decide

private theorem k11t8p10_initial_decoded_eq_row_8 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) 8 j = k11t8p10_state_0 8 j := by decide

private theorem k11t8p10_initial_decoded_eq_row_9 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) 9 j = k11t8p10_state_0 9 j := by decide

private theorem k11t8p10_initial_decoded_eq_row_10 : ∀ j : Fin 11, (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) 10 j = k11t8p10_state_0 10 j := by decide

private theorem k11t8p10_initial_decoded_eq : (fun i j => decode 12 (k11t8p10_template_mask i j) ∪ requiredMatrix 11 k11t8p10.required i j) = k11t8p10_state_0 := by
  funext i j
  fin_cases i

  · exact k11t8p10_initial_decoded_eq_row_0 j

  · exact k11t8p10_initial_decoded_eq_row_1 j

  · exact k11t8p10_initial_decoded_eq_row_2 j

  · exact k11t8p10_initial_decoded_eq_row_3 j

  · exact k11t8p10_initial_decoded_eq_row_4 j

  · exact k11t8p10_initial_decoded_eq_row_5 j

  · exact k11t8p10_initial_decoded_eq_row_6 j

  · exact k11t8p10_initial_decoded_eq_row_7 j

  · exact k11t8p10_initial_decoded_eq_row_8 j

  · exact k11t8p10_initial_decoded_eq_row_9 j

  · exact k11t8p10_initial_decoded_eq_row_10 j

private theorem k11t8p10_initial_eq : k11t8p10.initialMatrix 11 = k11t8p10_state_0 := by
  have h := decode_templateMaskMatrix 12 k11t8p10_mask_entries k11t8p10_decode_entries
  rw [k11t8p10_mask_entries_map, k11t8p10_template_mask_eq] at h
  funext i j
  change templateMatrix k11t8p10.templates i j ∪ requiredMatrix 11 k11t8p10.required i j = _
  rw [← congrFun (congrFun h i) j]
  exact congrFun (congrFun k11t8p10_initial_decoded_eq i) j

private theorem k11t8p10_closure_0 : ClosureCheck k11t8p10.graph k11t8p10_state_0 11 8 [] := by trivial

private theorem k11t8p10_matrix_eq : k11t8p10.matrix 11 = k11t8p10_state_0 := by
  change closureMatrix (k11t8p10.initialMatrix 11) _ = _
  rw [k11t8p10_initial_eq]
  change closureMatrix k11t8p10_state_0 [] = _
  rfl

private theorem k11t8p10_part_0 : k11t8p10.chains.flatten = List.finRange _ := by decide

private theorem k11t8p10_part_1 : k11t8p10.chains.map List.length = ([[], [], [1], [1], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k11t8p10_part_2 : k11t8p10.chains.map (fun l => l.map (fun i => decide (i ∈ k11t8p10.clique))) = ([[], [], [1], [1], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k11t8p10_templates_item_0 : (⟨0, 1, [[2, 3, 4]], [], [], 2, 7⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_1 : (⟨0, 1, [[2, 3, 4], [5, 6, 7], [8, 9, 10]], [], [], 1, 1⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_2 : (⟨0, 2, [[5, 6, 7], [8, 9, 10]], [], [3, 4], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_3 : (⟨0, 3, [[5, 6, 7]], [], [2], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_4 : (⟨0, 4, [[5, 6, 7], [8, 9, 10]], [], [3, 2], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_5 : (⟨0, 5, [[2, 3, 4], [8, 9, 10]], [], [6, 7], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_6 : (⟨0, 6, [[2, 3, 4]], [], [5], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_7 : (⟨0, 7, [[2, 3, 4], [8, 9, 10]], [], [6, 5], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_8 : (⟨0, 8, [[2, 3, 4], [5, 6, 7]], [], [9, 10], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_9 : (⟨1, 2, [], [], [3, 4], 2, 8⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_10 : (⟨1, 2, [[5, 6, 7], [8, 9, 10]], [], [3, 4], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_11 : (⟨1, 3, [[5, 6, 7]], [], [2], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_12 : (⟨1, 4, [[5, 6, 7], [8, 9, 10]], [], [3, 2], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_13 : (⟨1, 5, [[2, 3, 4], [8, 9, 10]], [], [6, 7], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_14 : (⟨1, 6, [[2, 3, 4]], [], [5], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_15 : (⟨1, 7, [[2, 3, 4], [8, 9, 10]], [], [6, 5], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_16 : (⟨1, 8, [[2, 3, 4], [5, 6, 7]], [], [9, 10], 1, 2⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_17 : (⟨2, 3, [[5, 6, 7]], [], [4], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_18 : (⟨2, 6, [], [4, 3], [5], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_19 : (⟨3, 4, [[5, 6, 7]], [2], [], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_20 : (⟨3, 5, [], [2], [6, 7], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_21 : (⟨3, 6, [], [2], [5], 1, 8⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_22 : (⟨3, 7, [], [2], [6, 5], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_23 : (⟨3, 8, [[5, 6, 7]], [2], [], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_24 : (⟨4, 6, [], [2, 3], [5], 1, 7⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_25 : (⟨5, 6, [[2, 3, 4]], [], [7], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_26 : (⟨6, 7, [[2, 3, 4]], [5], [], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_item_27 : (⟨6, 8, [[2, 3, 4]], [5], [], 1, 6⟩ : TemplateData (Fin 11)).Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  rw [← k11t8p10_tableGraph_eq]
  decide

private theorem k11t8p10_templates_fast_block_0_check : ∀ T ∈ k11t8p10_mask_entries_0.map Prod.fst, T.Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k11t8p10_mask_entries_0, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k11t8p10_templates_item_0, k11t8p10_templates_item_1, k11t8p10_templates_item_2, k11t8p10_templates_item_3, k11t8p10_templates_item_4, k11t8p10_templates_item_5, k11t8p10_templates_item_6, k11t8p10_templates_item_7, k11t8p10_templates_item_8, k11t8p10_templates_item_9, k11t8p10_templates_item_10, k11t8p10_templates_item_11, k11t8p10_templates_item_12, k11t8p10_templates_item_13, k11t8p10_templates_item_14, k11t8p10_templates_item_15, k11t8p10_templates_item_16, k11t8p10_templates_item_17, k11t8p10_templates_item_18, k11t8p10_templates_item_19, k11t8p10_templates_item_20, k11t8p10_templates_item_21, k11t8p10_templates_item_22, k11t8p10_templates_item_23, k11t8p10_templates_item_24, k11t8p10_templates_item_25, k11t8p10_templates_item_26, k11t8p10_templates_item_27⟩

private theorem k11t8p10_part_3 : ∀ T ∈ k11t8p10.templates, T.Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k11t8p10_mask_entries_0.map Prod.fst), T.Check k11t8p10.graph k11t8p10.clique 11 (patternAmount ([[], [], [1], [1], [1]] : List (List ℕ))) (([[], [], [1], [1], [1]] : List (List ℕ)).map List.length).sum
  exact k11t8p10_templates_fast_block_0_check

private theorem k11t8p10_part_4 : ∀ p ∈ k11t8p10.required, p.Check k11t8p10.graph 11 := by decide

private theorem k11t8p10_part_5 : ClosureCheck k11t8p10.graph (k11t8p10.initialMatrix 11) 11 8 k11t8p10.closure := by
  rw [k11t8p10_initial_eq]
  exact k11t8p10_closure_0

private theorem k11t8p10_part_6 : k11t8p10.bad.Check k11t8p10.graph (k11t8p10.matrix 11) 11 8 := by
  rw [k11t8p10_matrix_eq]
  decide

theorem k11t8p10_check : k11t8p10.Check 11 8 [[], [], [1], [1], [1]] :=
  ⟨k11t8p10_part_0, k11t8p10_part_1, k11t8p10_part_2, k11t8p10_part_3, k11t8p10_part_4, k11t8p10_part_5, k11t8p10_part_6⟩
end CycleClique.Construction.Certificates

end OAI
