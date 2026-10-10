import OAI.Computability.PerfectCompleteness.Algebra.BucketMatrixResampling
import OAI.Computability.PerfectCompleteness.Algebra.HierarchicalMatrixTable
import OAI.Computability.PerfectCompleteness.Foundations.WholeArrayInteriorExteriorLemmas
import OAI.Computability.PerfectCompleteness.Machines.OriginalWholeCutTape

namespace OAI

section

namespace PerfectCompleteness.CutNodeRows

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {N cut t : Nat}

theorem nativeH_eq (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :
    (H (cutSlots p slots) : Type) = (NodeEmbedding.NodeH slots (upperNode p) : Type) :=
  (congrArg (fun z : Σ h, Path branch N h => (H (cutSlots z.2 slots) : Type))
    (upperNode_spec p)).symm

def nativeEquiv : {N cut : Nat} → (p : Path branch N (cut + 1)) →
    (slots : Slots branch N → Fin t → MixedSupport.Slot) →
      H (cutSlots p slots) ≃ₗ[F2] NodeEmbedding.NodeH slots (upperNode p)
  | _, _, .refl _, _ => LinearEquiv.refl F2 _
  | _, _, .step i p, slots => nativeEquiv p (childSlots slots i)

def cutRowEquiv (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :
    H (cutSlots p slots) ≃ₗ[F2] NodeEmbedding.RowSpace slots (upperNode p) :=
  (nativeEquiv p slots).trans (NodeEmbedding.equiv slots (upperNode p))

def rowIndexEquiv (rows : Nat → Nat) (p : Path branch N (cut + 1)) :
    Fin (rows (cut + 1)) ≃ Fin (rows (Nodes.height (upperNode p))) :=
  Equiv.cast (congrArg (fun height => Fin (rows height)) (upperNode_height p).symm)

def directionEquiv (rows : Nat → Nat) (p : Path branch N (cut + 1)) :
    BucketSampler.Direction (rows (cut + 1)) ≃
      BucketSampler.Direction (rows (Nodes.height (upperNode p))) :=
  Equiv.cast (congrArg (fun height => BucketSampler.Direction (rows height))
    (upperNode_height p).symm)

theorem native_selectedRows (rows : Nat → Nat) :
    {N cut : Nat} → (p : Path branch N (cut + 1)) →
      (slots : Slots branch N → Fin t → MixedSupport.Slot) → (arrays : Arrays slots rows) →
      (fun i => nativeEquiv p slots
        (SelectedArrayReplacement.selectedRows rows p slots arrays ((rowIndexEquiv rows p).symm i))) =
        arrays (upperNode p)
  | _, _, .refl _, _, _ => rfl
  | _, _, .step i p, slots, arrays =>
      native_selectedRows rows p (childSlots slots i) (fun node => arrays (.inr (i, node)))

def transportRows (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (fresh : Fin (rows (cut + 1)) → H (cutSlots p slots)) :
    Fin (rows (Nodes.height (upperNode p))) → NodeEmbedding.RowSpace slots (upperNode p) :=
  fun i => cutRowEquiv p slots (fresh ((rowIndexEquiv rows p).symm i))

theorem transportRows_selectedRows (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    transportRows rows p slots (SelectedArrayReplacement.selectedRows rows p slots arrays) =
      NodeEmbedding.embeddedRows arrays (upperNode p) := by
  funext i
  exact congrArg (NodeEmbedding.embed slots (upperNode p))
    (congrFun (native_selectedRows rows p slots arrays) i)

def matrixOfRows (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (fresh : Fin (rows (cut + 1)) → H (cutSlots p slots)) :
    HierarchicalMatrixTable.Matrix (rows := rows) slots (upperNode p) :=
  EvaluationMatrix.ofRows (NodeEmbedding.RowSpace slots (upperNode p))
    (transportRows rows p slots fresh)

theorem ofRows_selectedRows (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    EvaluationMatrix.ofRows (NodeEmbedding.RowSpace slots (upperNode p))
        (transportRows rows p slots (SelectedArrayReplacement.selectedRows rows p slots arrays)) =
      NodeEmbedding.matrix arrays (upperNode p) := by
  rw [transportRows_selectedRows]
  rfl

theorem matrixOfRows_selectedRows (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    matrixOfRows rows p slots (SelectedArrayReplacement.selectedRows rows p slots arrays) =
      NodeEmbedding.matrix arrays (upperNode p) :=
  ofRows_selectedRows rows p slots arrays

def bucketTapeEquiv (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :
    BucketSampler.Tape (rows (cut + 1)) (H (cutSlots p slots)) ≃
      BucketSampler.Tape (rows (Nodes.height (upperNode p)))
        (NodeEmbedding.RowSpace slots (upperNode p)) :=
  Equiv.arrowCongr (directionEquiv rows p) (cutRowEquiv p slots).toEquiv

def bucketSampleEquiv (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :
    (BucketSampler.Direction (rows (cut + 1)) ×
      (BucketSampler.Tape (rows (cut + 1)) (H (cutSlots p slots)) × H (cutSlots p slots))) ≃
    (BucketSampler.Direction (rows (Nodes.height (upperNode p))) ×
      (BucketSampler.Tape (rows (Nodes.height (upperNode p)))
        (NodeEmbedding.RowSpace slots (upperNode p)) ×
          NodeEmbedding.RowSpace slots (upperNode p))) :=
  (directionEquiv rows p).prodCongr
    ((bucketTapeEquiv rows p slots).prodCongr (cutRowEquiv p slots).toEquiv)

private theorem tape_equiv_update {V W : Type*} {ℓ ℓ' : Nat} (h : ℓ = ℓ')
    (e : V ≃ W) (tape : BucketSampler.Tape ℓ V) (a : BucketSampler.Direction ℓ) (fresh : V) :
    Equiv.arrowCongr (Equiv.cast (congrArg BucketSampler.Direction h)) e
        (Function.update tape a fresh) =
      Function.update
        (Equiv.arrowCongr (Equiv.cast (congrArg BucketSampler.Direction h)) e tape)
        (Equiv.cast (congrArg BucketSampler.Direction h) a) (e fresh) := by
  cases h
  funext d
  change e (Function.update tape a fresh d) =
    Function.update (fun v => e (tape v)) a (e fresh) d
  exact Function.apply_update (fun (_ : BucketSampler.Direction ℓ) (v : V) => e v)
    tape a fresh d

theorem bucketTapeEquiv_update (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (tape : BucketSampler.Tape (rows (cut + 1)) (H (cutSlots p slots)))
    (a : BucketSampler.Direction (rows (cut + 1))) (fresh : H (cutSlots p slots)) :
    bucketTapeEquiv rows p slots (Function.update tape a fresh) =
      Function.update (bucketTapeEquiv rows p slots tape)
        (directionEquiv rows p a) (cutRowEquiv p slots fresh) :=
  tape_equiv_update (congrArg rows (upperNode_height p)).symm
    (cutRowEquiv p slots).toEquiv tape a fresh

private theorem evaluate_equiv {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module F2 V] [Module F2 W] {ℓ ℓ' : Nat} (h : ℓ = ℓ')
    (e : V ≃ₗ[F2] W) (tape : BucketSampler.Tape ℓ V) :
    (fun i => e (BucketSampler.evaluate ℓ (id : V → V) tape
        ((Equiv.cast (congrArg Fin h)).symm i))) =
      BucketSampler.evaluate ℓ' (id : W → W)
        (Equiv.arrowCongr (Equiv.cast (congrArg BucketSampler.Direction h)) e.toEquiv tape) := by
  cases h
  funext i
  change e (∑ v : BucketSampler.Direction ℓ, v.val i • tape v) =
    ∑ v : BucketSampler.Direction ℓ, v.val i • e (tape v)
  simp only [map_sum, map_smul]

theorem transportRows_evaluate (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (tape : BucketSampler.Tape (rows (cut + 1)) (H (cutSlots p slots))) :
    transportRows rows p slots
        (BucketSampler.evaluate (rows (cut + 1)) (id : H (cutSlots p slots) → _) tape) =
      BucketSampler.evaluate (rows (Nodes.height (upperNode p)))
        (id : NodeEmbedding.RowSpace slots (upperNode p) → _) (bucketTapeEquiv rows p slots tape) :=
  evaluate_equiv (congrArg rows (upperNode_height p)).symm (cutRowEquiv p slots) tape

theorem matrixOfRows_evaluate (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (tape : BucketSampler.Tape (rows (cut + 1)) (H (cutSlots p slots))) :
    matrixOfRows rows p slots
        (BucketSampler.evaluate (rows (cut + 1)) (id : H (cutSlots p slots) → _) tape) =
      BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots (upperNode p))
        (rows (Nodes.height (upperNode p))) (bucketTapeEquiv rows p slots tape) := by
  unfold matrixOfRows BucketMatrixResampling.assembledMatrix
  rw [transportRows_evaluate]

end
end PerfectCompleteness.CutNodeRows

end

end OAI
