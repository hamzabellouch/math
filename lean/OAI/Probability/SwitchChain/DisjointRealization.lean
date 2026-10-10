import OAI.Probability.SwitchChain.DisjointBoundary
import OAI.Probability.SwitchChain.DisjointInternal

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

variable {V : Type*} [sectionFintypeV : Fintype V]

def crossCode (e : Fin 4 ↪ V) (G : SimpleGraph V) : CrossBlock.Matrix :=
  fun a b => decide (G.Adj (e (leftIndex a)) (e (rightIndex b)))

def leftAssignment (e : Fin 4 ↪ V) (G H : SimpleGraph V) :
    Finset {w : V // Outside e w} :=
  (BinaryAssignments.singletons (leftCounts e G)).filter (fun w => H.Adj (e 0) w.val)

def rightAssignment (e : Fin 4 ↪ V) (G H : SimpleGraph V) :
    Finset {w : V // Outside e w} :=
  (BinaryAssignments.singletons (rightCounts e G)).filter (fun w => H.Adj (e 2) w.val)

def realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w}) : SimpleGraph V :=
  reconstruct e (internalGraph (decide (G.Adj (e 0) (e 1)))
    (decide (G.Adj (e 2) (e 3))) M) (assignmentBoundary e G U W) (G.comap Subtype.val)

theorem realizeCoordinates_sameCell (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G))
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    SameCell e G (realizeCoordinates e G M U W) := by
  apply sameCell_reconstruct
  · simp
  · simp
  · exact assignmentBoundary_matches e G U W hU hW

@[simp] theorem crossCode_realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w}) :
    crossCode e (realizeCoordinates e G M U W) = M := by
  have retainedsectionFintypeV := sectionFintypeV
  funext a b
  simp [crossCode, realizeCoordinates]

theorem leftAssignment_realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G)) :
    leftAssignment e G (realizeCoordinates e G M U W) = U := by
  ext w
  simp only [leftAssignment, Finset.mem_filter, realizeCoordinates,
    reconstruct_block_outside]
  change (w ∈ BinaryAssignments.singletons (leftCounts e G) ∧
    BinaryAssignments.first (leftCounts e G) U w) ↔ w ∈ U
  constructor
  · intro h
    exact (BinaryAssignments.first_on_singletons _ U w h.1).mp h.2
  · intro h
    exact ⟨hU h, (BinaryAssignments.first_on_singletons _ U w (hU h)).mpr h⟩

theorem rightAssignment_realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    rightAssignment e G (realizeCoordinates e G M U W) = W := by
  ext w
  simp only [rightAssignment, Finset.mem_filter, realizeCoordinates,
    reconstruct_block_outside]
  change (w ∈ BinaryAssignments.singletons (rightCounts e G) ∧
    BinaryAssignments.first (rightCounts e G) W w) ↔ w ∈ W
  constructor
  · intro h
    exact (BinaryAssignments.first_on_singletons _ W w h.1).mp h.2
  · intro h
    exact ⟨hW h, (BinaryAssignments.first_on_singletons _ W w (hW h)).mpr h⟩

theorem feasible_coordinates_realized (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G))
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G))
    (hdegree : ∀ a,
      (internalGraph (decide (G.Adj (e 0) (e 1))) (decide (G.Adj (e 2) (e 3))) M).degree a +
        (Finset.univ.filter (assignmentBoundary e G U W a)).card = G.degree (e a)) :
    ∃ H : SimpleGraph V, SameCell e G H ∧ (∀ v, H.degree v = G.degree v) ∧
      crossCode e H = M ∧ leftAssignment e G H = U ∧ rightAssignment e G H = W := by
  refine ⟨realizeCoordinates e G M U W, realizeCoordinates_sameCell e G M U W hU hW,
    ?_, crossCode_realizeCoordinates e G M U W,
    leftAssignment_realizeCoordinates e G M U W hU,
    rightAssignment_realizeCoordinates e G M U W hW⟩
  exact degree_preserved_of_block e G _ _ (assignmentBoundary_matches e G U W hU hW) hdegree

theorem first_edge_iff_of_counts (G H K : SimpleGraph V) (i j w : V)
    (hH : edgeBit G i w + edgeBit G j w = edgeBit H i w + edgeBit H j w)
    (hK : edgeBit G i w + edgeBit G j w = edgeBit K i w + edgeBit K j w)
    (hsingle : edgeBit G i w + edgeBit G j w = 1 → (H.Adj i w ↔ K.Adj i w)) :
    H.Adj i w ↔ K.Adj i w := by
  by_cases h : edgeBit G i w + edgeBit G j w = 1
  · exact hsingle h
  · apply (edgeBit_eq_iff H K i w).mp
    have hHi := edgeBit_le_one H i w
    have hHj := edgeBit_le_one H j w
    have hKi := edgeBit_le_one K i w
    have hKj := edgeBit_le_one K j w
    omega

theorem graph_eq_of_cell_assignments (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K)
    (hM : crossCode e H = crossCode e K)
    (hU : leftAssignment e G H = leftAssignment e G K)
    (hW : rightAssignment e G H = rightAssignment e G K) : H = K := by
  apply graph_eq_of_cell_coordinates e H K (hH.symm.trans hK)
  constructor
  · have h := congrFun (congrFun hM 0) 0
    simpa [crossCode, leftIndex, rightIndex] using h
  · have h := congrFun (congrFun hM 0) 1
    simpa [crossCode, leftIndex, rightIndex] using h
  · have h := congrFun (congrFun hM 1) 0
    simpa [crossCode, leftIndex, rightIndex] using h
  · have h := congrFun (congrFun hM 1) 1
    simpa [crossCode, leftIndex, rightIndex] using h
  · intro w hw
    apply first_edge_iff_of_counts G H K (e 0) (e 1) w
      (hH.leftCount w hw) (hK.leftCount w hw)
    intro hs
    have h := Finset.ext_iff.mp hU ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (leftCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
  · intro w hw
    apply first_edge_iff_of_counts G H K (e 2) (e 3) w
      (hH.rightCount w hw) (hK.rightCount w hw)
    intro hs
    have h := Finset.ext_iff.mp hW ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (rightCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2

theorem realizeCoordinates_encode (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hH : SameCell e G H) :
    realizeCoordinates e G (crossCode e H) (leftAssignment e G H)
      (rightAssignment e G H) = H := by
  have hU : leftAssignment e G H ⊆ BinaryAssignments.singletons (leftCounts e G) :=
    Finset.filter_subset _ _
  have hW : rightAssignment e G H ⊆ BinaryAssignments.singletons (rightCounts e G) :=
    Finset.filter_subset _ _
  apply graph_eq_of_cell_assignments e G _ H
    (realizeCoordinates_sameCell e G _ _ _ hU hW) hH
  · exact crossCode_realizeCoordinates e G _ _ _
  · exact leftAssignment_realizeCoordinates e G _ _ _ hU
  · exact rightAssignment_realizeCoordinates e G _ _ _ hW

@[ext] structure FeasibleCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V) where
  matrix : CrossBlock.Matrix
  left : Finset {w : V // Outside e w}
  right : Finset {w : V // Outside e w}
  left_subset : left ⊆ BinaryAssignments.singletons (leftCounts e G)
  right_subset : right ⊆ BinaryAssignments.singletons (rightCounts e G)
  degrees : ∀ a,
    (internalGraph (decide (G.Adj (e 0) (e 1))) (decide (G.Adj (e 2) (e 3))) matrix).degree a +
      (Finset.univ.filter (assignmentBoundary e G left right a)).card = G.degree (e a)

abbrev DegreeCell (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  {H : SimpleGraph V // SameCell e G H ∧ ∀ v, H.degree v = G.degree v}

def cellEncode (e : Fin 4 ↪ V) (G : SimpleGraph V) (H : DegreeCell e G) :
    FeasibleCoordinates e G where
  matrix := crossCode e H.val
  left := leftAssignment e G H.val
  right := rightAssignment e G H.val
  left_subset := Finset.filter_subset _ _
  right_subset := Finset.filter_subset _ _
  degrees := by
    intro a
    have h := congrArg (fun K : SimpleGraph V => K.degree (e a))
      (realizeCoordinates_encode e G H.val H.property.1)
    unfold realizeCoordinates at h
    rw [degree_reconstruct_block] at h
    exact h.trans (H.property.2 (e a))

def cellDecode (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    DegreeCell e G :=
  ⟨realizeCoordinates e G c.matrix c.left c.right,
    realizeCoordinates_sameCell e G _ _ _ c.left_subset c.right_subset,
    degree_preserved_of_block e G _ _
      (assignmentBoundary_matches e G _ _ c.left_subset c.right_subset) c.degrees⟩

def degreeCellEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    DegreeCell e G ≃ FeasibleCoordinates e G where
  toFun := cellEncode e G
  invFun := cellDecode e G
  left_inv H := by
    apply Subtype.ext
    exact realizeCoordinates_encode e G H.val H.property.1
  right_inv c := by
    apply FeasibleCoordinates.ext
    · exact crossCode_realizeCoordinates e G _ _ _
    · exact leftAssignment_realizeCoordinates e G _ _ _ c.left_subset
    · exact rightAssignment_realizeCoordinates e G _ _ _ c.right_subset

end Problem315.DisjointEncoding

end

end OAI
