import OAI.Computability.PerfectCompleteness.Decoding.LowerCutNodeCoordinates

namespace OAI

section

namespace PerfectCompleteness.LowerCutNodeMatrix

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit WholeArrayInteriorExterior LowerCutNodeCoordinates
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

abbrev NativeMatrix (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Module.Dual F2 (H (subtreeSlots p slots)) →ₗ[F2] (Fin (rows (m + 1)) → F2)

abbrev NodeMatrix (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Module.Dual F2 (H (nodeSlots slots (upperNode p))) →ₗ[F2] Block rows (upperNode p)

def matrixEquiv (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
    (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      NativeMatrix rows p slots ≃ₗ[F2] NodeMatrix rows p slots
  | _, _, .refl _, _ => LinearEquiv.refl F2 _
  | _, _, .step i p, slots => matrixEquiv rows p (childSlots slots i)

theorem ofRows_transport (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
    (slots : Slots branch n → Fin t → MixedSupport.Slot) →
    (S : Fin (rows (m + 1)) → H (subtreeSlots p slots)) →
      matrixEquiv rows p slots (EvaluationMatrix.ofRows (H (subtreeSlots p slots)) S) =
        EvaluationMatrix.ofRows (H (nodeSlots slots (upperNode p))) (rowEquiv rows p slots S)
  | _, _, .refl _, _, _ => rfl
  | _, _, .step i p, slots, S => ofRows_transport rows p (childSlots slots i) S

theorem rows_transport (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
    (slots : Slots branch n → Fin t → MixedSupport.Slot) →
    (X : NativeMatrix rows p slots) →
      EvaluationMatrix.rows (H (nodeSlots slots (upperNode p))) (matrixEquiv rows p slots X) =
        rowEquiv rows p slots (EvaluationMatrix.rows (H (subtreeSlots p slots)) X)
  | _, _, .refl _, _, _ => rfl
  | _, _, .step i p, slots, X => rows_transport rows p (childSlots slots i) X

theorem selectedRows_matrix (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    matrixEquiv rows p slots
        (EvaluationMatrix.ofRows (H (subtreeSlots p slots))
          (SelectedArrayReplacement.selectedRows rows p slots arrays)) =
      EvaluationMatrix.ofRows (H (nodeSlots slots (upperNode p))) (arrays (upperNode p)) := by
  rw [ofRows_transport, rowEquiv_selectedRows]

theorem shift_transport (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
    (slots : Slots branch n → Fin t → MixedSupport.Slot) →
    (X : NativeMatrix rows p slots) →
    (a : BucketSampler.Direction (rows (m + 1))) →
    (h : H (subtreeSlots p slots)) →
      matrixEquiv rows p slots (EvaluationMatrix.shift (H (subtreeSlots p slots)) X a.val h) =
        EvaluationMatrix.shift (H (nodeSlots slots (upperNode p))) (matrixEquiv rows p slots X)
          (directionEquiv rows p a).val (scalarEquiv p slots h)
  | _, _, .refl _, _, _, _, _ => rfl
  | _, _, .step i p, slots, X, a, h =>
      shift_transport rows p (childSlots slots i) X a h

theorem replace_matrix_transport (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (a : BucketSampler.Direction (rows (m + 1)))
    (S : Fin (rows (m + 1)) → H (subtreeSlots p slots))
    (fresh : H (subtreeSlots p slots)) :
    matrixEquiv rows p slots
        (EvaluationMatrix.ofRows (H (subtreeSlots p slots))
          (LowerDirectionFiber.replace a S fresh)) =
      EvaluationMatrix.ofRows (H (nodeSlots slots (upperNode p)))
        (LowerDirectionFiber.replace (directionEquiv rows p a)
          (rowEquiv rows p slots S) (scalarEquiv p slots fresh)) := by
  rw [ofRows_transport, rowEquiv_replace]

section Laws

open UniqueGamesTheorem.Foundations.Games

variable (rows : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)

local instance nativeMatrixFintype : Fintype (NativeMatrix rows p slots) :=
  Fintype.ofEquiv (Fin (rows (m + 1)) → H (subtreeSlots p slots))
    (EvaluationMatrix.rowsEquiv (H (subtreeSlots p slots))).symm

local instance nodeMatrixFintype : Fintype (NodeMatrix rows p slots) :=
  Fintype.ofEquiv (Fin (rows (Nodes.height (upperNode p))) → H (nodeSlots slots (upperNode p)))
    (EvaluationMatrix.rowsEquiv (H (nodeSlots slots (upperNode p)))).symm

theorem uniform_matrixEquiv :
    (FiniteDistribution.uniform (NativeMatrix rows p slots)).pushforward
        (matrixEquiv rows p slots) =
      FiniteDistribution.uniform (NodeMatrix rows p slots) := by
  have h := UniformConditioning.uniform_transport (matrixEquiv rows p slots).toEquiv
  rw [FiniteDistribution.transport_eq_pushforward] at h
  exact h

theorem uniform_matrix_scalarEquiv :
    ((FiniteDistribution.uniform (NativeMatrix rows p slots)).product
      (FiniteDistribution.uniform (H (subtreeSlots p slots)))).pushforward
        (fun z => (matrixEquiv rows p slots z.1, scalarEquiv p slots z.2)) =
      (FiniteDistribution.uniform (NodeMatrix rows p slots)).product
        (FiniteDistribution.uniform (H (nodeSlots slots (upperNode p)))) := by
  have hscalar :
      (FiniteDistribution.uniform (H (subtreeSlots p slots))).pushforward
          (scalarEquiv p slots) =
        FiniteDistribution.uniform (H (nodeSlots slots (upperNode p))) := by
    have h := UniformConditioning.uniform_transport (scalarEquiv p slots).toEquiv
    rw [FiniteDistribution.transport_eq_pushforward] at h
    exact h
  rw [FiniteDistribution.product_pushforward, uniform_matrixEquiv rows p slots, hscalar]

theorem uniform_stepPair_transport (a : BucketSampler.Direction (rows (m + 1))) :
    (((FiniteDistribution.uniform (NativeMatrix rows p slots)).product
      (FiniteDistribution.uniform (H (subtreeSlots p slots)))).pushforward
        (fun z => (z.1, EvaluationMatrix.shift (H (subtreeSlots p slots)) z.1 a.val z.2))).pushforward
          (fun z => (matrixEquiv rows p slots z.1, matrixEquiv rows p slots z.2)) =
      ((FiniteDistribution.uniform (NodeMatrix rows p slots)).product
        (FiniteDistribution.uniform (H (nodeSlots slots (upperNode p))))).pushforward
          (fun z => (z.1, EvaluationMatrix.shift (H (nodeSlots slots (upperNode p))) z.1
            (directionEquiv rows p a).val z.2)) := by
  have h := congrArg
    (fun μ : FiniteDistribution
        (NodeMatrix rows p slots × H (nodeSlots slots (upperNode p))) =>
      μ.pushforward (fun z =>
        (z.1, EvaluationMatrix.shift (H (nodeSlots slots (upperNode p))) z.1
          (directionEquiv rows p a).val z.2)))
    (uniform_matrix_scalarEquiv rows p slots)
  rw [FiniteDistribution.pushforward_comp] at h
  rw [FiniteDistribution.pushforward_comp]
  simpa only [shift_transport] using h

end Laws

end
end PerfectCompleteness.LowerCutNodeMatrix

end

end OAI
