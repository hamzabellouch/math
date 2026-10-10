import OAI.Computability.PerfectCompleteness.Algebra.ChildBilinearCollisionTransfer
import OAI.Computability.PerfectCompleteness.Decoding.ChildAssemblyProjection
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutNodeCoordinates
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutRowsLemmas
import OAI.Computability.PerfectCompleteness.Decoding.LowerDirectionFiber
import OAI.Computability.PerfectCompleteness.Foundations.CutCallExtension
import OAI.Computability.PerfectCompleteness.Foundations.MultiplicationFormInjectiveLemmas
import OAI.Computability.PerfectCompleteness.Machines.LowerCutDecoderInput
import OAI.Computability.PerfectCompleteness.Machines.OwnInputReferenceLemmas

namespace OAI

section

namespace PerfectCompleteness.LowerCutPair

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)

abbrev Calls := WholeCutCalls.Index rows repeats p
abbrev Raw := CutCallExtension.Extended (C := Calls rows repeats p) (cutSlots p slots) rows
abbrev NativeRows := Fin (rows (m + 1)) → H (cutSlots p slots)
abbrev NativeMatrix := Module.Dual F2 (H (cutSlots p slots)) →ₗ[F2] (Fin (rows (m + 1)) → F2)

def first (exterior : Exterior rows repeats p slots) (raw : Raw rows repeats p slots) :
    Arrays slots rows :=
  LowerCutRows.reconstruct rows repeats p slots exterior
    (CutCallExtension.original (cutSlots p slots) rows raw)

def fresh (raw : Raw rows repeats p slots) : H (cutSlots p slots) :=
  CutCallExtension.fresh (cutSlots p slots) rows raw

def second (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots) :
    Arrays slots rows :=
  SelectedArrayReplacement.replace rows p slots (first rows repeats p slots exterior raw)
    (LowerDirectionFiber.replace a
      (SelectedArrayReplacement.selectedRows rows p slots (first rows repeats p slots exterior raw))
      (fresh rows repeats p slots raw))

def arraysPair (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots) :
    Arrays slots rows × Arrays slots rows :=
  (first rows repeats p slots exterior raw, second rows repeats p slots exterior a raw)

@[simp] theorem selected_second (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots) :
    SelectedArrayReplacement.selectedRows rows p slots (second rows repeats p slots exterior a raw) =
      LowerDirectionFiber.replace a
        (SelectedArrayReplacement.selectedRows rows p slots (first rows repeats p slots exterior raw))
        (fresh rows repeats p slots raw) :=
  SelectedArrayReplacement.selectedRows_replace rows p slots _ _

theorem second_outside (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots)
    (node : Nodes branch n) (hne : node ≠ WholeArrayInteriorExterior.upperNode p) :
    second rows repeats p slots exterior a raw node =
      first rows repeats p slots exterior raw node :=
  SelectedArrayReplacement.replace_outside rows p slots _ _ node hne

theorem selected_quotient (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots) :
    LowerDirectionFiber.quotientQuery (H (cutSlots p slots)) a
        (SelectedArrayReplacement.selectedRows rows p slots
          (second rows repeats p slots exterior a raw)) =
      LowerDirectionFiber.quotientQuery (H (cutSlots p slots)) a
        (SelectedArrayReplacement.selectedRows rows p slots
          (first rows repeats p slots exterior raw)) := by
  rw [selected_second]
  exact LowerDirectionFiber.quotientQuery_replace _ _ _ _

def readRowsFresh (exterior : Exterior rows repeats p slots) (raw : Raw rows repeats p slots) :
    NativeRows rows p slots × H (cutSlots p slots) :=
  (SelectedArrayReplacement.selectedRows rows p slots (first rows repeats p slots exterior raw),
    fresh rows repeats p slots raw)

def selectPair :
    (CutChildGrouping.Assembled (C := Calls rows repeats p) (cutSlots p slots) rows ×
      H (cutSlots p slots)) →ₗ[F2] (NativeRows rows p slots × H (cutSlots p slots)) :=
  (LowerCutRows.selectRows rows repeats p slots).prodMap LinearMap.id

theorem selectPair_surjective : Function.Surjective (selectPair rows repeats p slots) := by
  rintro ⟨S, h⟩
  obtain ⟨record, hrecord⟩ := LowerCutRows.selectRows_surjective rows repeats p slots S
  exact ⟨(record, h), Prod.ext hrecord rfl⟩

@[simp] theorem readRowsFresh_eq (exterior : Exterior rows repeats p slots)
    (raw : Raw rows repeats p slots) :
    readRowsFresh rows repeats p slots exterior raw =
      selectPair rows repeats p slots
        (CutCallExtension.observe (cutSlots p slots) rows raw) := by
  apply Prod.ext
  · exact LowerCutRows.selectedRows_reconstruct_eq rows repeats p slots exterior _
  · rfl

theorem readRowsFresh_law (exterior : Exterior rows repeats p slots) :
    (CutChildGrouping.rawLaw (C := Option (Calls rows repeats p)) (cutSlots p slots) rows).pushforward
        (readRowsFresh rows repeats p slots exterior) =
      (FiniteDistribution.uniform (NativeRows rows p slots)).product
        (FiniteDistribution.uniform (H (cutSlots p slots))) := by
  change (CutChildGrouping.rawLaw (C := Option (Calls rows repeats p)) (cutSlots p slots) rows).pushforward
    (fun raw => readRowsFresh rows repeats p slots exterior raw) = _
  simp only [readRowsFresh_eq]
  rw [← FiniteDistribution.pushforward_comp, CutCallExtension.observe_law,
    WholeCutSampler.uniform_product,
    UniformLinearImage.uniform_pushforward_linearMap
      (selectPair rows repeats p slots) (selectPair_surjective rows repeats p slots)]
  exact WholeCutSampler.uniform_product.symm

def selectedPair (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots) :
    NativeRows rows p slots × NativeRows rows p slots :=
  (SelectedArrayReplacement.selectedRows rows p slots (first rows repeats p slots exterior raw),
    SelectedArrayReplacement.selectedRows rows p slots (second rows repeats p slots exterior a raw))

theorem selectedPair_law (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (CutChildGrouping.rawLaw (C := Option (Calls rows repeats p)) (cutSlots p slots) rows).pushforward
        (selectedPair rows repeats p slots exterior a) =
      LowerDirectionFiber.fiberPairLaw (H := H (cutSlots p slots)) a := by
  have h := congrArg
    (fun μ : FiniteDistribution (NativeRows rows p slots × H (cutSlots p slots)) =>
      μ.pushforward (fun z => (z.1, LowerDirectionFiber.replace a z.1 z.2)))
    (readRowsFresh_law rows repeats p slots exterior)
  rw [FiniteDistribution.pushforward_comp, LowerDirectionFiber.two_copy_law] at h
  change (CutChildGrouping.rawLaw (C := Option (Calls rows repeats p)) (cutSlots p slots) rows).pushforward
    (fun raw =>
      (SelectedArrayReplacement.selectedRows rows p slots (first rows repeats p slots exterior raw),
        SelectedArrayReplacement.selectedRows rows p slots (second rows repeats p slots exterior a raw))) = _
  simpa only [readRowsFresh, selected_second] using h

def matrixPair (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots) :
    NativeMatrix rows p slots × NativeMatrix rows p slots :=
  let z := selectedPair rows repeats p slots exterior a raw
  (EvaluationMatrix.ofRows (H (cutSlots p slots)) z.1,
    EvaluationMatrix.ofRows (H (cutSlots p slots)) z.2)

local instance nativeMatrixFintype : Fintype (NativeMatrix rows p slots) :=
  Fintype.ofEquiv (NativeRows rows p slots) (EvaluationMatrix.rowsEquiv (H (cutSlots p slots))).symm

theorem matrixPair_law (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (CutChildGrouping.rawLaw (C := Option (Calls rows repeats p)) (cutSlots p slots) rows).pushforward
        (matrixPair rows repeats p slots exterior a) =
      ((FiniteDistribution.uniform (NativeMatrix rows p slots)).product
        (FiniteDistribution.uniform (H (cutSlots p slots)))).pushforward
          (fun z => (z.1, EvaluationMatrix.shift (H (cutSlots p slots)) z.1 a.val z.2)) := by
  have h := congrArg
    (fun μ : FiniteDistribution (NativeRows rows p slots × NativeRows rows p slots) =>
      μ.pushforward (fun z => (EvaluationMatrix.ofRows (H (cutSlots p slots)) z.1,
        EvaluationMatrix.ofRows (H (cutSlots p slots)) z.2)))
    (selectedPair_law rows repeats p slots exterior a)
  rw [FiniteDistribution.pushforward_comp, LowerDirectionFiber.matrix_pair_law] at h
  exact h

end
end PerfectCompleteness.LowerCutPair

end

section

namespace PerfectCompleteness.LowerCutDecoderForm

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping

variable {branch rows repeats : Nat → Nat} {n height t : Nat}
  (path : Path branch n (height + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

def spaceEquiv : H (cutSlots path slots) ≃ₗ[ZMod 2]
    HierarchicalDecoderTables.LowerH slots upper lowerLevel d :=
  (LowerCutNodeCoordinates.scalarEquiv path slots).trans (by
    rw [hnode])

def form (answer : HierarchicalDecoderTables.Answer slots upper lowerLevel d) :
    ChildBilinearCollisionTransfer.ParentForm (cutSlots path slots) where
  toFun f := (OddListExtraction.multiplicationForm
    (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) answer
      (spaceEquiv path slots upper lowerLevel d hnode f)).comp
        (spaceEquiv path slots upper lowerLevel d hnode).toLinearMap
  map_add' f g := by
    ext h
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' c f := by
    ext h
    simp only [LinearMap.comp_apply, map_smul,
      LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem form_apply
    (answer : HierarchicalDecoderTables.Answer slots upper lowerLevel d)
    (f g : H (cutSlots path slots)) :
    form path slots upper lowerLevel d hnode answer f g =
      OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) answer
        (spaceEquiv path slots upper lowerLevel d hnode f)
        (spaceEquiv path slots upper lowerLevel d hnode g) := rfl

theorem form_injective :
    Function.Injective (form path slots upper lowerLevel d hnode) := by
  intro answer answer' hform
  apply MultiplicationFormInjective.multiplicationForm_injective
    (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
  ext f g
  obtain ⟨f', rfl⟩ := (spaceEquiv path slots upper lowerLevel d hnode).surjective f
  obtain ⟨g', rfl⟩ := (spaceEquiv path slots upper lowerLevel d hnode).surjective g
  exact congrArg (fun F : ChildBilinearCollisionTransfer.ParentForm
    (cutSlots path slots) => F f' g') hform

variable (hbranch : ∀ k < n, 0 < branch k) {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (table : HierarchicalAllDecoderTables.Input (rows := rows)
    slots upper lowerLevel adviceRows → HierarchicalAllDecoderTables.UpperAnswer slots upper)
  (cutoff : Nat)

def answer (arrays : Arrays slots rows) :
    Option (HierarchicalDecoderTables.Answer slots upper lowerLevel d) :=
  HierarchicalDecoderTables.decode slots upper lowerLevel hbranch d cutoff
    (table (LowerCutDecoderInput.actualInput slots upper lowerLevel arrays A))

def readForm (arrays : Arrays slots rows) :
    Option (ChildBilinearCollisionTransfer.ParentForm (cutSlots path slots)) :=
  (answer slots upper lowerLevel d hbranch A table cutoff arrays).map
    (form path slots upper lowerLevel d hnode)

def first (exterior : Exterior rows repeats path slots)
    (raw : LowerCutPair.Raw rows repeats path slots) :
    Option (ChildBilinearCollisionTransfer.ParentForm (cutSlots path slots)) :=
  readForm path slots upper lowerLevel d hnode hbranch A table cutoff
    (LowerCutPair.first rows repeats path slots exterior raw)

def second (exterior : Exterior rows repeats path slots)
    (direction : BucketSampler.Direction (rows (height + 1)))
    (raw : LowerCutPair.Raw rows repeats path slots) :
    Option (ChildBilinearCollisionTransfer.ParentForm (cutSlots path slots)) :=
  readForm path slots upper lowerLevel d hnode hbranch A table cutoff
    (LowerCutPair.second rows repeats path slots exterior direction raw)

theorem fullCollision_readForm (arrays arrays' : Arrays slots rows) :
    BilinearCollisionTransfer.fullCollision
        (readForm path slots upper lowerLevel d hnode hbranch A table cutoff arrays)
        (readForm path slots upper lowerLevel d hnode hbranch A table cutoff arrays') =
      DecoderTableCoupling.definedEqual
        (answer slots upper lowerLevel d hbranch A table cutoff arrays)
        (answer slots upper lowerLevel d hbranch A table cutoff arrays') :=
  MultiplicationFormInjective.definedEqual_map_of_injective
    (form path slots upper lowerLevel d hnode)
    (form_injective path slots upper lowerLevel d hnode) _ _

theorem fullCollision_pair (exterior : Exterior rows repeats path slots)
    (direction : BucketSampler.Direction (rows (height + 1)))
    (raw : LowerCutPair.Raw rows repeats path slots) :
    BilinearCollisionTransfer.fullCollision
        (first path slots upper lowerLevel d hnode hbranch A table cutoff exterior raw)
        (second path slots upper lowerLevel d hnode hbranch A table cutoff exterior direction raw) =
      TwoResponseCollision.collision
        (answer slots upper lowerLevel d hbranch A table cutoff)
        (LowerCutPair.arraysPair rows repeats path slots exterior direction raw) :=
  fullCollision_readForm path slots upper lowerLevel d hnode hbranch A table cutoff _ _

end
end PerfectCompleteness.LowerCutDecoderForm

end

end OAI
