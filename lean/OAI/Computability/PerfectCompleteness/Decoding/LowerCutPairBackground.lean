import OAI.Computability.PerfectCompleteness.Algebra.HierarchicalMatrixTable
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutNodeCoordinates
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutPairLemmas
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutRowsLemmas

namespace OAI

section

namespace PerfectCompleteness.LowerCutPairBackground

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)

abbrev Complement := LowerCutCallSplit.Complement rows repeats p slots
abbrev NativeRows := LowerCutPair.NativeRows rows p slots
abbrev NativeMatrix := LowerCutPair.NativeMatrix rows p slots

abbrev Observation := Complement rows repeats p slots ×
  (NativeRows rows p slots × H (cutSlots p slots))

def splitObservation :
    (CutChildGrouping.Assembled (C := LowerCutPair.Calls rows repeats p)
      (cutSlots p slots) rows × H (cutSlots p slots)) →ₗ[F2]
      Observation rows repeats p slots where
  toFun z :=
    ((LowerCutCallSplit.splitAssembled rows repeats p slots z.1).1,
      ((LowerCutCallSplit.splitAssembled rows repeats p slots z.1).2, z.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem splitObservation_surjective :
    Function.Surjective (splitObservation rows repeats p slots) := by
  rintro ⟨c, S, h⟩
  obtain ⟨record, hrecord⟩ :=
    LowerCutCallSplit.splitAssembled_surjective rows repeats p slots (c, S)
  refine ⟨(record, h), ?_⟩
  change ((LowerCutCallSplit.splitAssembled rows repeats p slots record).1,
    ((LowerCutCallSplit.splitAssembled rows repeats p slots record).2, h)) = (c, S, h)
  rw [hrecord]

def observe (raw : LowerCutPair.Raw rows repeats p slots) :
    Observation rows repeats p slots :=
  splitObservation rows repeats p slots (CutCallExtension.observe (cutSlots p slots) rows raw)

theorem observe_law :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
      (cutSlots p slots) rows).pushforward (observe rows repeats p slots) =
      (FiniteDistribution.uniform (Complement rows repeats p slots)).product
        ((FiniteDistribution.uniform (NativeRows rows p slots)).product
          (FiniteDistribution.uniform (H (cutSlots p slots)))) := by
  change (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
    (cutSlots p slots) rows).pushforward
      (fun raw => splitObservation rows repeats p slots
        (CutCallExtension.observe (cutSlots p slots) rows raw)) = _
  rw [← FiniteDistribution.pushforward_comp, CutCallExtension.observe_law,
    WholeCutSampler.uniform_product,
    UniformLinearImage.uniform_pushforward_linearMap
      (splitObservation rows repeats p slots) (splitObservation_surjective rows repeats p slots)]
  rw [WholeCutSampler.uniform_product, WholeCutSampler.uniform_product]

@[simp] theorem observe_rows (exterior : Exterior rows repeats p slots)
    (raw : LowerCutPair.Raw rows repeats p slots) :
    (observe rows repeats p slots raw).2.1 =
      SelectedArrayReplacement.selectedRows rows p slots
        (LowerCutPair.first rows repeats p slots exterior raw) := by
  exact (LowerCutRows.selectedRows_reconstruct_eq rows repeats p slots exterior _).symm

@[simp] theorem observe_fresh (raw : LowerCutPair.Raw rows repeats p slots) :
    (observe rows repeats p slots raw).2.2 = LowerCutPair.fresh rows repeats p slots raw := rfl

def rowPair (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats p slots) :
    Complement rows repeats p slots × (NativeRows rows p slots × NativeRows rows p slots) :=
  ((observe rows repeats p slots raw).1,
    LowerCutPair.selectedPair rows repeats p slots exterior a raw)

theorem rowPair_law (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
      (cutSlots p slots) rows).pushforward (rowPair rows repeats p slots exterior a) =
      (FiniteDistribution.uniform (Complement rows repeats p slots)).product
        (LowerDirectionFiber.fiberPairLaw (H := H (cutSlots p slots)) a) := by
  have h := congrArg
    (fun μ : FiniteDistribution (Observation rows repeats p slots) => μ.pushforward
      (fun z => (z.1, (z.2.1, LowerDirectionFiber.replace a z.2.1 z.2.2))))
    (observe_law rows repeats p slots)
  rw [FiniteDistribution.pushforward_comp] at h
  have hp := FiniteDistribution.product_pushforward
      (FiniteDistribution.uniform (Complement rows repeats p slots))
      ((FiniteDistribution.uniform (NativeRows rows p slots)).product
        (FiniteDistribution.uniform (H (cutSlots p slots))))
      (id : Complement rows repeats p slots → Complement rows repeats p slots)
      (fun z => (z.1, LowerDirectionFiber.replace a z.1 z.2))
  simp only [FiniteDistribution.pushforward_id, id_eq, LowerDirectionFiber.two_copy_law] at hp
  have hfinal := h.trans hp
  change (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
    (cutSlots p slots) rows).pushforward (fun raw =>
      ((observe rows repeats p slots raw).1,
        (SelectedArrayReplacement.selectedRows rows p slots
          (LowerCutPair.first rows repeats p slots exterior raw),
         SelectedArrayReplacement.selectedRows rows p slots
          (LowerCutPair.second rows repeats p slots exterior a raw)))) = _
  simpa only [LowerCutPair.selected_second,
    observe_rows rows repeats p slots exterior, observe_fresh] using hfinal

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

def matrixPair (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats p slots) :
    Complement rows repeats p slots × (NativeMatrix rows p slots × NativeMatrix rows p slots) :=
  ((observe rows repeats p slots raw).1,
    LowerCutPair.matrixPair rows repeats p slots exterior a raw)

theorem matrixPair_law (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
      (cutSlots p slots) rows).pushforward (matrixPair rows repeats p slots exterior a) =
      (FiniteDistribution.uniform (Complement rows repeats p slots)).product
        (((FiniteDistribution.uniform (NativeMatrix rows p slots)).product
          (FiniteDistribution.uniform (H (cutSlots p slots)))).pushforward
            (fun z => (z.1, EvaluationMatrix.shift (H (cutSlots p slots)) z.1 a.val z.2))) := by
  have h := congrArg
    (fun μ : FiniteDistribution
      (Complement rows repeats p slots × (NativeRows rows p slots × NativeRows rows p slots)) =>
      μ.pushforward (fun z => (z.1,
        (EvaluationMatrix.ofRows (H (cutSlots p slots)) z.2.1,
          EvaluationMatrix.ofRows (H (cutSlots p slots)) z.2.2))))
    (rowPair_law rows repeats p slots exterior a)
  rw [FiniteDistribution.pushforward_comp] at h
  have hp := FiniteDistribution.product_pushforward
      (FiniteDistribution.uniform (Complement rows repeats p slots))
      (LowerDirectionFiber.fiberPairLaw (H := H (cutSlots p slots)) a)
      (id : Complement rows repeats p slots → Complement rows repeats p slots)
      (fun z => (EvaluationMatrix.ofRows (H (cutSlots p slots)) z.1,
        EvaluationMatrix.ofRows (H (cutSlots p slots)) z.2))
  simp only [FiniteDistribution.pushforward_id, id_eq, LowerDirectionFiber.matrix_pair_law] at hp
  exact h.trans hp

def backgroundArrays (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) : Arrays slots rows :=
  LowerCutAssembled.reconstruct rows repeats p slots exterior
    (LowerCutCallSplit.merge rows repeats p slots c 0)

def installRows (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) (S : NativeRows rows p slots) : Arrays slots rows :=
  SelectedArrayReplacement.replace rows p slots
    (backgroundArrays rows repeats p slots exterior c) S

theorem reconstruct_merge (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) (S : NativeRows rows p slots) :
    LowerCutAssembled.reconstruct rows repeats p slots exterior
        (LowerCutCallSplit.merge rows repeats p slots c S) =
      installRows rows repeats p slots exterior c S := by
  have h := LowerCutAssembled.reconstruct_congr_replace rows repeats p slots exterior
    (LowerCutCallSplit.merge rows repeats p slots c 0)
    (LowerCutCallSplit.merge rows repeats p slots c S)
    (fun call hcall =>
      (LowerCutCallSplit.merge_otherCall rows repeats p slots c S ⟨call, hcall⟩).trans
        (LowerCutCallSplit.merge_otherCall rows repeats p slots c 0 ⟨call, hcall⟩).symm) rfl
  rw [LowerCutCallSplit.selectRows_merge] at h
  exact h

theorem first_eq_installRows (exterior : Exterior rows repeats p slots)
    (raw : LowerCutPair.Raw rows repeats p slots) :
    LowerCutPair.first rows repeats p slots exterior raw =
      installRows rows repeats p slots exterior (observe rows repeats p slots raw).1
        (SelectedArrayReplacement.selectedRows rows p slots
          (LowerCutPair.first rows repeats p slots exterior raw)) := by
  rw [← observe_rows rows repeats p slots exterior]
  change LowerCutRows.reconstruct rows repeats p slots exterior
      (CutCallExtension.original (cutSlots p slots) rows raw) =
    installRows rows repeats p slots exterior
      (LowerCutCallSplit.splitAssembled rows repeats p slots
        (CutChildGrouping.assemble (cutSlots p slots) rows
          (CutCallExtension.original (cutSlots p slots) rows raw))).1
      (LowerCutCallSplit.splitAssembled rows repeats p slots
        (CutChildGrouping.assemble (cutSlots p slots) rows
          (CutCallExtension.original (cutSlots p slots) rows raw))).2
  rw [← LowerCutAssembled.reconstruct_assemble, ← reconstruct_merge,
    LowerCutCallSplit.merge_split]

private theorem replace_replace (arrays : Arrays slots rows)
    (S T : NativeRows rows p slots) :
    SelectedArrayReplacement.replace rows p slots
        (SelectedArrayReplacement.replace rows p slots arrays S) T =
      SelectedArrayReplacement.replace rows p slots arrays T := by
  simp only [LowerCutNodeCoordinates.replace_eq_update]
  funext node
  by_cases hnode : node = WholeArrayInteriorExterior.upperNode p
  · subst node
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hnode]

theorem second_eq_installRows (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats p slots) :
    LowerCutPair.second rows repeats p slots exterior a raw =
      installRows rows repeats p slots exterior (observe rows repeats p slots raw).1
        (SelectedArrayReplacement.selectedRows rows p slots
          (LowerCutPair.second rows repeats p slots exterior a raw)) := by
  rw [LowerCutPair.selected_second]
  exact (congrArg
    (fun arrays => SelectedArrayReplacement.replace rows p slots arrays
      (LowerDirectionFiber.replace a
        (SelectedArrayReplacement.selectedRows rows p slots
          (LowerCutPair.first rows repeats p slots exterior raw))
        (LowerCutPair.fresh rows repeats p slots raw)))
    (first_eq_installRows rows repeats p slots exterior raw)).trans
      (replace_replace rows p slots _ _ _)

def installMatrix (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) (X : NativeMatrix rows p slots) : Arrays slots rows :=
  installRows rows repeats p slots exterior c (EvaluationMatrix.rows (H (cutSlots p slots)) X)

theorem arraysPair_eq (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats p slots) :
    LowerCutPair.arraysPair rows repeats p slots exterior a raw =
      (installMatrix rows repeats p slots exterior (matrixPair rows repeats p slots exterior a raw).1
        (matrixPair rows repeats p slots exterior a raw).2.1,
       installMatrix rows repeats p slots exterior (matrixPair rows repeats p slots exterior a raw).1
        (matrixPair rows repeats p slots exterior a raw).2.2) := by
  simp only [matrixPair, LowerCutPair.matrixPair, LowerCutPair.selectedPair,
    installMatrix, EvaluationMatrix.rows_ofRows]
  exact Prod.ext (first_eq_installRows rows repeats p slots exterior raw)
    (second_eq_installRows rows repeats p slots exterior a raw)

theorem arraysPair_law (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
      (cutSlots p slots) rows).pushforward (LowerCutPair.arraysPair rows repeats p slots exterior a) =
      ((FiniteDistribution.uniform (Complement rows repeats p slots)).product
        (((FiniteDistribution.uniform (NativeMatrix rows p slots)).product
          (FiniteDistribution.uniform (H (cutSlots p slots)))).pushforward
            (fun z => (z.1, EvaluationMatrix.shift (H (cutSlots p slots)) z.1 a.val z.2)))).pushforward
        (fun z => (installMatrix rows repeats p slots exterior z.1 z.2.1,
          installMatrix rows repeats p slots exterior z.1 z.2.2)) := by
  have h := congrArg
    (fun μ : FiniteDistribution
      (Complement rows repeats p slots × (NativeMatrix rows p slots × NativeMatrix rows p slots)) =>
      μ.pushforward (fun z => (installMatrix rows repeats p slots exterior z.1 z.2.1,
        installMatrix rows repeats p slots exterior z.1 z.2.2)))
    (matrixPair_law rows repeats p slots exterior a)
  rw [FiniteDistribution.pushforward_comp] at h
  simpa only [← arraysPair_eq] using h

theorem installMatrix_eq_update (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) (X : NativeMatrix rows p slots) :
    installMatrix rows repeats p slots exterior c X =
      Function.update (backgroundArrays rows repeats p slots exterior c)
        (WholeArrayInteriorExterior.upperNode p)
        (LowerCutNodeCoordinates.rowEquiv rows p slots
          (EvaluationMatrix.rows (H (cutSlots p slots)) X)) :=
  LowerCutNodeCoordinates.replace_eq_update rows p slots _ _

theorem installMatrix_outside (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) (X : NativeMatrix rows p slots)
    (node : Nodes branch n) (hne : node ≠ WholeArrayInteriorExterior.upperNode p) :
    installMatrix rows repeats p slots exterior c X node =
      backgroundArrays rows repeats p slots exterior c node :=
  SelectedArrayReplacement.replace_outside rows p slots _ _ node hne

theorem backgroundOf_installMatrix (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) (X : NativeMatrix rows p slots) :
    HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
        (installMatrix rows repeats p slots exterior c X) =
      HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
        (backgroundArrays rows repeats p slots exterior c) := by
  funext node
  exact installMatrix_outside rows repeats p slots exterior c X node.val node.property

theorem upperMatrix_installMatrix (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) (X : NativeMatrix rows p slots)
    (upper : Nodes branch n) (hne : upper ≠ WholeArrayInteriorExterior.upperNode p) :
    NodeEmbedding.matrix (installMatrix rows repeats p slots exterior c X) upper =
      NodeEmbedding.matrix (backgroundArrays rows repeats p slots exterior c) upper := by
  unfold NodeEmbedding.matrix NodeEmbedding.embeddedRows
  rw [installMatrix_outside rows repeats p slots exterior c X upper hne]

end
end PerfectCompleteness.LowerCutPairBackground

end

end OAI
