import OAI.Computability.PerfectCompleteness.Algebra.LowerCutNodeMatrix
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutPairBackground
import OAI.Computability.PerfectCompleteness.Machines.LowerCutDecoderInput

namespace OAI

section

namespace PerfectCompleteness.LowerCutInstalledInput

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

section NodeEquality

variable (rows : Nat → Nat) (slots : Slots branch n → Fin t → MixedSupport.Slot)

abbrev NodeRows (node : Nodes branch n) := Fin (rows (Nodes.height node)) → H (nodeSlots slots node)
abbrev NodeMatrix (node : Nodes branch n) :=
  Module.Dual F2 (H (nodeSlots slots node)) →ₗ[F2] Block rows node

def rowCast {i j : Nodes branch n} (h : i = j) :
    NodeRows rows slots i ≃ₗ[F2] NodeRows rows slots j := by
  subst j
  exact LinearEquiv.refl F2 _

def matrixCast {i j : Nodes branch n} (h : i = j) :
    NodeMatrix rows slots i ≃ₗ[F2] NodeMatrix rows slots j := by
  subst j
  exact LinearEquiv.refl F2 _

def scalarCast {i j : Nodes branch n} (h : i = j) :
    H (nodeSlots slots i) ≃ₗ[F2] H (nodeSlots slots j) := by
  subst j
  exact LinearEquiv.refl F2 _

def directionCast {i j : Nodes branch n} (h : i = j) :
    BucketSampler.Direction (rows (Nodes.height i)) ≃
      BucketSampler.Direction (rows (Nodes.height j)) := by
  subst j
  exact Equiv.refl _

theorem rows_matrixCast {i j : Nodes branch n} (h : i = j)
    (X : NodeMatrix rows slots i) :
    EvaluationMatrix.rows (H (nodeSlots slots j)) (matrixCast rows slots h X) =
      rowCast rows slots h (EvaluationMatrix.rows (H (nodeSlots slots i)) X) := by
  subst j
  rfl

theorem shift_matrixCast {i j : Nodes branch n} (h : i = j)
    (X : NodeMatrix rows slots i) (a : BucketSampler.Direction (rows (Nodes.height i)))
    (v : H (nodeSlots slots i)) :
    matrixCast rows slots h (EvaluationMatrix.shift (H (nodeSlots slots i)) X a.val v) =
      EvaluationMatrix.shift (H (nodeSlots slots j)) (matrixCast rows slots h X)
        (directionCast rows h a).val (scalarCast slots h v) := by
  subst j
  rfl

theorem update_rowCast {i j : Nodes branch n} (h : i = j)
    (arrays : Arrays slots rows) (S : NodeRows rows slots i) :
    Function.update arrays i S = Function.update arrays j (rowCast rows slots h S) := by
  subst j
  rfl

end NodeEquality

variable (rows : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode p =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

def lowerMatrixEquiv : LowerCutPair.NativeMatrix rows p slots ≃ₗ[F2]
    HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d :=
  (LowerCutNodeMatrix.matrixEquiv rows p slots).trans (matrixCast rows slots hnode)

def lowerScalarEquiv : H (WholeCutGrouping.cutSlots p slots) ≃ₗ[F2]
    HierarchicalDecoderTables.LowerH slots upper lowerLevel d :=
  (LowerCutNodeCoordinates.scalarEquiv p slots).trans (scalarCast slots hnode)

def lowerDirectionEquiv : BucketSampler.Direction (rows (m + 1)) ≃
    BucketSampler.Direction (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) :=
  (LowerCutNodeCoordinates.directionEquiv rows p).trans (directionCast rows hnode)

theorem rows_lowerMatrixEquiv (X : LowerCutPair.NativeMatrix rows p slots) :
    EvaluationMatrix.rows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (lowerMatrixEquiv rows p slots upper lowerLevel d hnode X) =
      rowCast rows slots hnode
        (LowerCutNodeCoordinates.rowEquiv rows p slots
          (EvaluationMatrix.rows (H (WholeCutGrouping.cutSlots p slots)) X)) := by
  change EvaluationMatrix.rows (H (nodeSlots slots (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))
    (matrixCast rows slots hnode (LowerCutNodeMatrix.matrixEquiv rows p slots X)) = _
  rw [rows_matrixCast, LowerCutNodeMatrix.rows_transport]

theorem shift_lowerMatrixEquiv (X : LowerCutPair.NativeMatrix rows p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (v : H (WholeCutGrouping.cutSlots p slots)) :
    lowerMatrixEquiv rows p slots upper lowerLevel d hnode
        (EvaluationMatrix.shift (H (WholeCutGrouping.cutSlots p slots)) X a.val v) =
      EvaluationMatrix.shift (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (lowerMatrixEquiv rows p slots upper lowerLevel d hnode X)
        (lowerDirectionEquiv rows p upper lowerLevel d hnode a).val
        (lowerScalarEquiv p slots upper lowerLevel d hnode v) := by
  change matrixCast rows slots hnode
    (LowerCutNodeMatrix.matrixEquiv rows p slots
      (EvaluationMatrix.shift (H (WholeCutGrouping.cutSlots p slots)) X a.val v)) = _
  rw [LowerCutNodeMatrix.shift_transport]
  exact shift_matrixCast rows slots hnode (LowerCutNodeMatrix.matrixEquiv rows p slots X)
    (LowerCutNodeCoordinates.directionEquiv rows p a)
    (LowerCutNodeCoordinates.scalarEquiv p slots v)

local instance nativeMatrixFintype : Fintype (LowerCutPair.NativeMatrix rows p slots) :=
  Fintype.ofEquiv (LowerCutPair.NativeRows rows p slots)
    (EvaluationMatrix.rowsEquiv (H (WholeCutGrouping.cutSlots p slots))).symm
local instance lowerMatrixFintype : Fintype
    (HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d) :=
  Fintype.ofEquiv
    (Fin (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) →
      HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
    (EvaluationMatrix.rowsEquiv (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)).symm

theorem uniform_lowerMatrixEquiv :
    (FiniteDistribution.uniform (LowerCutPair.NativeMatrix rows p slots)).pushforward
        (lowerMatrixEquiv rows p slots upper lowerLevel d hnode) =
      FiniteDistribution.uniform
        (HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d) := by
  have h := UniformConditioning.uniform_transport
    (lowerMatrixEquiv rows p slots upper lowerLevel d hnode).toEquiv
  rw [FiniteDistribution.transport_eq_pushforward] at h
  exact h

theorem uniform_lowerMatrix_scalarEquiv :
    ((FiniteDistribution.uniform (LowerCutPair.NativeMatrix rows p slots)).product
      (FiniteDistribution.uniform (H (WholeCutGrouping.cutSlots p slots)))).pushforward
        (fun z => (lowerMatrixEquiv rows p slots upper lowerLevel d hnode z.1,
          lowerScalarEquiv p slots upper lowerLevel d hnode z.2)) =
      (FiniteDistribution.uniform
        (HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d)).product
        (FiniteDistribution.uniform (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)) := by
  have hscalar :
      (FiniteDistribution.uniform (H (WholeCutGrouping.cutSlots p slots))).pushforward
          (lowerScalarEquiv p slots upper lowerLevel d hnode) =
        FiniteDistribution.uniform (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := by
    have h := UniformConditioning.uniform_transport
      (lowerScalarEquiv p slots upper lowerLevel d hnode).toEquiv
    rw [FiniteDistribution.transport_eq_pushforward] at h
    exact h
  rw [FiniteDistribution.product_pushforward, uniform_lowerMatrixEquiv, hscalar]

variable (repeats : Nat → Nat)

theorem actualInput_installMatrix {r : Nat}
    (exterior : WholeCutGrouping.Exterior rows repeats p slots)
    (c : LowerCutPairBackground.Complement rows repeats p slots)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : LowerCutPair.NativeMatrix rows p slots) :
    LowerCutDecoderInput.actualInput slots upper lowerLevel
        (LowerCutPairBackground.installMatrix rows repeats p slots exterior c X) A =
      HierarchicalLowerMatrixInput.input slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper
          (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c)) d
        (NodeEmbedding.matrix (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c) upper)
        A (lowerMatrixEquiv rows p slots upper lowerLevel d hnode X) := by
  rw [LowerCutPairBackground.installMatrix_eq_update, update_rowCast rows slots hnode]
  have h := LowerCutDecoderInput.actualInput_update slots upper lowerLevel
    (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c) d A
    (rowCast rows slots hnode (LowerCutNodeCoordinates.rowEquiv rows p slots
      (EvaluationMatrix.rows (H (WholeCutGrouping.cutSlots p slots)) X)))
  have hX : EvaluationMatrix.ofRows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
      (rowCast rows slots hnode (LowerCutNodeCoordinates.rowEquiv rows p slots
        (EvaluationMatrix.rows (H (WholeCutGrouping.cutSlots p slots)) X))) =
      lowerMatrixEquiv rows p slots upper lowerLevel d hnode X := by
    rw [← rows_lowerMatrixEquiv rows p slots upper lowerLevel d hnode,
      EvaluationMatrix.ofRows_rows]
  rw [hX] at h
  exact h

end
end PerfectCompleteness.LowerCutInstalledInput

end

end OAI
