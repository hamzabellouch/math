import OAI.Computability.PerfectCompleteness.Algebra.CanonicalMatrixTable
import OAI.Computability.PerfectCompleteness.Construction.NodeEmbedding

namespace OAI

section

namespace PerfectCompleteness.HierarchicalMatrixTable

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (node : Nodes branch n)

abbrev Background := (j : {j : Nodes branch n // j ≠ node}) →
  Fin (rows (Nodes.height j.val)) → NodeEmbedding.NodeH slots j.val

abbrev SideOutput : Type :=
  BlockQuotient.OtherBlocks (fun j : Nodes branch n => Block rows j) node × PUnit.{1}

abbrev Matrix := Module.Dual F2 (NodeEmbedding.RowSpace slots node) →ₗ[F2] Block rows node

def backgroundOf (arrays : Arrays slots rows) : Background (rows := rows) slots node :=
  fun j => arrays j.val

def nativeRows (X : Matrix (rows := rows) slots node) :
    Fin (rows (Nodes.height node)) → NodeEmbedding.NodeH slots node :=
  fun i => (NodeEmbedding.equiv slots node).symm
    (EvaluationMatrix.rows (NodeEmbedding.RowSpace slots node) X i)

def assemble (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) : Arrays slots rows :=
  fun j => if h : j = node then h.symm ▸ nativeRows slots node X else background ⟨j, h⟩

@[simp] theorem assemble_selected (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) :
    assemble slots node background X node = nativeRows slots node X := by
  simp [assemble]

@[simp] theorem assemble_other (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) (j : {j : Nodes branch n // j ≠ node}) :
    assemble slots node background X j.val = background j := by
  simp only [assemble, dite_eq_right j.property]

theorem embedded_assembled_rows (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) :
    NodeEmbedding.embeddedRows (assemble slots node background X) node =
      EvaluationMatrix.rows (NodeEmbedding.RowSpace slots node) X := by
  funext i
  change NodeEmbedding.embed slots node ((assemble slots node background X) node i) = _
  rw [assemble_selected]
  exact (NodeEmbedding.equiv slots node).apply_symm_apply _

theorem matrix_assemble (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) :
    NodeEmbedding.matrix (assemble slots node background X) node = X := by
  unfold NodeEmbedding.matrix
  rw [embedded_assembled_rows, EvaluationMatrix.ofRows_rows]

theorem nativeRows_matrix (arrays : Arrays slots rows) :
    nativeRows slots node (NodeEmbedding.matrix arrays node) = arrays node := by
  funext i
  change (NodeEmbedding.equiv slots node).symm
    (EvaluationMatrix.rows (NodeEmbedding.RowSpace slots node)
      (EvaluationMatrix.ofRows (NodeEmbedding.RowSpace slots node)
        (NodeEmbedding.embeddedRows arrays node)) i) = arrays node i
  rw [EvaluationMatrix.rows_ofRows]
  exact (NodeEmbedding.equiv slots node).symm_apply_apply _

theorem assemble_original (arrays : Arrays slots rows) :
    assemble slots node (backgroundOf slots node arrays) (NodeEmbedding.matrix arrays node) = arrays := by
  funext j
  by_cases hj : j = node
  · subst j
    rw [assemble_selected, nativeRows_matrix]
  · simp only [assemble, dite_eq_right hj, backgroundOf]

def other (background : Background (rows := rows) slots node)
    (x : NodeEmbedding.NumberedDomain slots) : SideOutput (rows := rows) node :=
  (fun j i => (background j i).val (NodeEmbedding.numberedRestriction slots j.val x), PUnit.unit)

def displayed (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) :
    NodeEmbedding.NumberedDomain slots → (Output branch n rows : Type) :=
  TreeCanonical.numberedFunction slots (fullJoint (assemble slots node background X))

theorem displayed_original (arrays : Arrays slots rows) :
    displayed slots node (backgroundOf slots node arrays) (NodeEmbedding.matrix arrays node) =
      TreeCanonical.numberedFunction slots (fullJoint arrays) := by
  unfold displayed
  rw [assemble_original]

theorem query_eq_split_displayed (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) :
    CanonicalMatrixTable.query (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots node) (other slots node background) X =
      BlockQuotient.splitOutput (fun j : Nodes branch n => Block rows j) PUnit.{1} node ∘
        displayed slots node background X := by
  funext x
  apply Prod.ext
  · change EvaluationMatrix.evaluate (NodeEmbedding.RowSpace slots node) X x =
      (displayed slots node background X x).1 node
    have he := NodeEmbedding.matrix_evaluate (assemble slots node background X) node x
    rw [matrix_assemble] at he
    exact he
  · apply Prod.ext
    · funext j i
      change (background j i).val (NodeEmbedding.numberedRestriction slots j.val x) =
        ((assemble slots node background X) j.val i).val
          (NodeEmbedding.numberedRestriction slots j.val x)
      rw [assemble_other]
    · rfl

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

theorem response_eq_split_response (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) :
    CanonicalMatrixTable.response (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots node) (other slots node background) σ X =
      BlockQuotient.splitOutput (fun j : Nodes branch n => Block rows j) PUnit.{1} node
        (KeyStrategy.response σ .left (TreeCanonical.numberedSlots slots)
          (displayed slots node background X)) := by
  unfold CanonicalMatrixTable.response
  rw [query_eq_split_displayed]
  exact KeyStrategy.response_postcomp_injective σ .left (TreeCanonical.numberedSlots slots)
    (displayed slots node background X)
    (BlockQuotient.splitOutput (fun j : Nodes branch n => Block rows j) PUnit.{1} node)
    (BlockQuotient.splitOutput (fun j : Nodes branch n => Block rows j) PUnit.{1} node).injective

theorem rightQuery_eq (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) (a : Block rows node) :
    CanonicalMatrixTable.rightQuery (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots node) (other slots node background) a X =
      BlockQuotient.projectBlock node a ∘ displayed slots node background X := by
  unfold CanonicalMatrixTable.rightQuery
  rw [query_eq_split_displayed]
  rfl

theorem accepts_iff_canonical (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) (a : Block rows node) :
    CanonicalMatrixTable.Accepts (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots node) (other slots node background) σ a X ↔
    CanonicalEdges.coarsen (TreeCanonical.numberedSlots slots)
      (displayed slots node background X) (BlockQuotient.projectBlock node a)
      (KeyStrategy.label σ .left (TreeCanonical.numberedSlots slots)
        (displayed slots node background X)) =
      KeyStrategy.label σ .right (TreeCanonical.numberedSlots slots)
        (BlockQuotient.projectBlock node a ∘ displayed slots node background X) := by
  have hresponse := congrArg (DirectionQuotient.projectWithSide a)
    (response_eq_split_response slots node σ background X)
  have hright := congrArg
    (KeyStrategy.response σ .right (TreeCanonical.numberedSlots slots))
    (rightQuery_eq slots node background X a)
  rw [CanonicalMatrixTable.accepts_iff, CanonicalEdges.coarsen_eq_iff]
  constructor
  · intro h
    exact hresponse.symm.trans (h.trans hright)
  · intro h
    exact hresponse.trans (h.trans hright.symm)

end
end PerfectCompleteness.HierarchicalMatrixTable

end

end OAI
