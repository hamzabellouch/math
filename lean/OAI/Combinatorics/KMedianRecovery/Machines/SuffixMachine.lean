import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.FiniteMachine
import OAI.Combinatorics.KMedianRecovery.Machines.SliceFold

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeRefinement
variable {X : Type*}
lemma cuts_prune (C U : List X) :
    (cuts U).map (fun p=>C++p.2.2)=CanonicalMergePath.pruneSuffix C U := by
  induction U generalizing C with
  | nil=>rfl
  | cons a U ih=>
    simp only [cuts,List.map_cons,List.map_map,Function.comp_def,CanonicalMergePath.pruneSuffix,ih]
lemma cuts_grow (C U : List X) (f : X) :
    ((cuts U).map (fun p=>(C++p.2.1::p.2.2)++[f])).reverse=growSuffix C f U := by
  induction U generalizing C with
  | nil=>rfl
  | cons a U ih=>
    simp only [cuts,List.map_cons,List.reverse_cons,List.map_map,Function.comp_def,growSuffix,ih]
end MetricKMedianRecovery.CanonicalMergeRefinement
namespace MetricKMedianRecovery.BitMachine.BinarySuffix
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
lemma slices_labels {m : ℕ} (U : List (Label (Fin m))) :
    Slices.run (labels U)=Slices.outBits BinaryLabel.encode (CanonicalMergeRefinement.cuts U) :=
  Slices.run_items BinaryLabel.encode U
lemma cut_fields {m : ℕ} (p : List (Label (Fin m)) × Label (Fin m) × List (Label (Fin m))) :
    field 0 (Slices.cutBits BinaryLabel.encode p)=labels p.1 ∧
    field 1 (Slices.cutBits BinaryLabel.encode p)=BinaryLabel.encode p.2.1 ∧
    field 2 (Slices.cutBits BinaryLabel.encode p)=labels p.2.2 := by
  simp [Slices.cutBits,Slices.itemsBits,field_encode,labels]
noncomputable def pruneOp (x : List Bool) : List Bool := extractPrefix x++field 2 (discardPrefix x)
noncomputable def pruneOp_computes : PolyComputes pruneOp := extractPrefix_computes.append (discardPrefix_computes.comp (field_computes 2))
noncomputable def pruneInput (x : List Bool) : List Bool := pairBits (extractPrefix x,Slices.run (discardPrefix x))
noncomputable def pruneInput_computes : PolyComputes pruneInput := extractPrefix_computes.pair (discardPrefix_computes.comp Slices.run_computes)
noncomputable def prune : List Bool → List Bool := mapWith pruneOp ∘ pruneInput
noncomputable def prune_computes : PolyComputes prune := pruneInput_computes.comp (mapWith_computes pruneOp_computes)
lemma prune_pack {m : ℕ} (C U : List (Label (Fin m))) :
    prune (pairBits (labels C,labels U))=historyBits (CanonicalMergePath.pruneSuffix C U) := by
  simp only [prune,Function.comp_apply,pruneInput,extractPrefix_pairBits,discardPrefix_pairBits,slices_labels,
    Slices.outBits,mapWith_encode,List.map_map,pruneOp,Function.comp_def,extractPrefix_pairBits,discardPrefix_pairBits]
  simp only [(cut_fields _).2.2,←BinaryFiniteContext.labels_append]
  rw [←CanonicalMergeRefinement.cuts_prune]
  simp only [historyBits,List.map_map,Function.comp_def]
noncomputable def growOp (x : List Bool) : List Bool :=
  extractPrefix (extractPrefix x)++cons (field 1 (discardPrefix x)) (field 2 (discardPrefix x))++
    cons (discardPrefix (extractPrefix x)) []
noncomputable def growOp_computes : PolyComputes growOp :=
  ((extractPrefix_computes.comp extractPrefix_computes).append
    (cons_computes (discardPrefix_computes.comp (field_computes 1)) (discardPrefix_computes.comp (field_computes 2)))).append
    (cons_computes (extractPrefix_computes.comp discardPrefix_computes) (const_computes []))
noncomputable def grow : List Bool → List Bool := reverse ∘ (mapWith growOp ∘ pruneInput)
noncomputable def grow_computes : PolyComputes grow :=
  (pruneInput_computes.comp (mapWith_computes growOp_computes)).comp WordList.reverse_computes
lemma grow_pack {m : ℕ} (C U : List (Label (Fin m))) (f : Label (Fin m)) :
    grow (pairBits (pairBits (labels C,BinaryLabel.encode f),labels U))=
      historyBits (CanonicalMergeRefinement.growSuffix C f U) := by
  simp only [grow,Function.comp_apply,pruneInput,extractPrefix_pairBits,discardPrefix_pairBits,slices_labels,
    Slices.outBits,mapWith_encode,List.map_map,growOp,Function.comp_def,extractPrefix_pairBits,discardPrefix_pairBits]
  simp only [(cut_fields _).2.1,(cut_fields _).2.2,←BinaryFiniteContext.labels_cons,←BinaryFiniteContext.labels_append]
  rw [show cons (BinaryLabel.encode f) []=labels [f] from rfl]
  simp only [←BinaryFiniteContext.labels_append]
  rw [reverse_encode,←CanonicalMergeRefinement.cuts_grow]
  simp only [historyBits,List.map_reverse,List.map_map,Function.comp_def]
end MetricKMedianRecovery.BitMachine.BinarySuffix

end OAI
