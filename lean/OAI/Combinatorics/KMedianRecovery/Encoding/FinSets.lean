import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Score
import OAI.Combinatorics.KMedianRecovery.Geometry.MetricParser
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionFillMath

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
def values (S : Finset (Fin n)) : Finset ℕ := S.image Fin.val
def encode (S : Finset (Fin n)) : List Bool := BinaryNatSet.encode (values S)
lemma values_card (S : Finset (Fin n)) : (values S).card=S.card := Finset.card_image_of_injective _ Fin.val_injective
lemma values_union (S T : Finset (Fin n)) : values (S∪T)=values S∪values T := Finset.image_union _ _
lemma values_diff (S T : Finset (Fin n)) : values (S\T)=values S\values T := by
  exact Finset.image_sdiff S T Fin.val_injective
lemma values_sort (S : Finset (Fin n)) : (values S).sort (·≤·)=(S.sort (·≤·)).map Fin.val := by
  let f : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  have hh := Finset.map_sort f S (·≤·) (·≤·) (fun a _ b _=>show a≤b↔a.val≤b.val from Iff.rfl)
  simpa only [f,Finset.map_eq_image,values,Function.Embedding.coeFn_mk] using hh.symm
lemma encode_eq (S : Finset (Fin n)) : encode S=WordList.encode ((S.sort (·≤·)).map (fun i=>i.val.bits)) := by
  rw [encode,BinaryNatSet.encode,BinaryNatSet.pack,values_sort,List.map_map]
  rfl
lemma values_bottom (S : Finset (Fin n)) (k : ℕ) :
    values (Completion.bottomSet S k)=Completion.bottomSet (values S) k := by
  unfold values Completion.bottomSet
  rw [show (Finset.image Fin.val S).sort (·≤·)=(S.sort (·≤·)).map Fin.val from values_sort S,←List.map_take]
  ext i
  simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
lemma values_pad (F U : Finset (Fin n)) (k : ℕ) :
    values (Completion.Canonical.pad F U k)=Completion.Canonical.pad (values F) (values U) k := by
  simp only [Completion.Canonical.pad,values_union,values_bottom,values_diff,values_card]
lemma union_pack (S T : Finset (Fin n)) : BinaryNatSet.union (pairBits (encode S,encode T))=encode (S∪T) := by
  rw [encode,encode,BinaryNatSet.union_encode,encode,values_union]
lemma diff_pack (S T : Finset (Fin n)) : BinaryNatSet.diff (pairBits (encode S,encode T))=encode (S\T) := by
  rw [encode,encode,BinaryNatSet.diff_encode,encode,values_diff]
lemma pad_pack (F U : Finset (Fin n)) (k : ℕ) :
    BinaryCompletionPad.run (WordList.encode [encode F,encode U,k.bits])=encode (Completion.Canonical.pad F U k) := by
  change BinaryCompletionPad.run (BinaryCompletionPad.pack (values F) (values U) k)=_
  rw [BinaryCompletionPad.run_pack,encode,values_pad]
end MetricKMedianRecovery.BitMachine.BinaryFinSet

namespace MetricKMedianRecovery.BitMachine.BinaryMaskParser
open WordOperations WordList
noncomputable def member (x : List Bool) : Bool :=
  (RawDrop.run (pairBits (discardPrefix x,extractPrefix x))).head?.getD false
noncomputable def member_computes : PolyComputes (fun x=>[member x]) :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp RawDrop.run_computes).comp MetricKMedianRecovery.BitMachine.head_computes
noncomputable def run (x : List Bool) : List Bool :=
  BinaryNatSet.sort (filterWith member (pairBits (x,BinaryEllipsoidInitial.indices (RawUnary.run x))))
noncomputable def run_computes : PolyComputes run :=
  (id_computes.pair (RawUnary.run_computes.comp BinaryEllipsoidInitial.indices_computes)).comp
    ((filterWith_computes member_computes).comp BinaryNatSet.sort_computes)
lemma member_mask {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    member (pairBits (BinaryInputParser.Metric.mask S,i.val.bits))=decide (i∈S) := by
  simp only [member,extractPrefix_pairBits,discardPrefix_pairBits,RawDrop.run_encode,
    BinaryInputParser.Metric.mask,List.head?_drop,List.getElem?_ofFn,Fin.eta]
  rw [dite_eq_left i.isLt,Option.getD_some]
lemma run_mask {n : ℕ} (S : Finset (Fin n)) :
    run (BinaryInputParser.Metric.mask S)=BinaryFinSet.encode S := by
  have hu : RawUnary.run (BinaryInputParser.Metric.mask S)=List.replicate n true := by
    simp only [RawUnary.run,BinaryInputParser.Metric.mask,List.length_ofFn]
  rw [run,hu,BinaryEllipsoidInitial.indices_replicate,filterWith_encode]
  have he : List.ofFn (fun i : Fin n=>i.val.bits)=(List.ofFn (fun i:Fin n=>i)).map (fun i=>i.val.bits) := by
    rw [List.map_ofFn]; rfl
  rw [he,List.filter_map]
  simp only [Function.comp_def,member_mask]
  let xs:=(List.ofFn (fun i:Fin n=>i)).filter (fun i=>decide (i∈S))
  have hs : xs.toFinset=S := by
    ext i
    simp only [xs,List.mem_toFinset,List.mem_filter,List.mem_ofFn,exists_apply_eq_apply,true_and,decide_eq_true_eq]
  change BinaryNatSet.sort (encode (xs.map (fun i=>i.val.bits)))=BinaryFinSet.encode S
  have hh:=BinaryNatSet.sort_pack (xs.map Fin.val)
  simp only [BinaryNatSet.pack,List.map_map,Function.comp_def] at hh
  rw [hh]
  change BinaryNatSet.encode ((xs.map Fin.val).toFinset)=BinaryNatSet.encode (BinaryFinSet.values S)
  congr 1
  ext v
  simp only [List.mem_toFinset,List.mem_map,BinaryFinSet.values,Finset.mem_image]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨i,by rw [←hs]; exact List.mem_toFinset.mpr hi,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨i,by apply List.mem_toFinset.mp; rw [hs]; exact hi,rfl⟩
end MetricKMedianRecovery.BitMachine.BinaryMaskParser

namespace MetricKMedianRecovery.BitMachine.BinaryIndexMap
open WordOperations WordList
noncomputable def item (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,extractPrefix x))
noncomputable def item_computes : PolyComputes item := (discardPrefix_computes.pair extractPrefix_computes).comp Lookup.run_computes
noncomputable def run : List Bool→List Bool := mapWith item
noncomputable def run_computes : PolyComputes run := mapWith_computes item_computes
lemma run_pack {α : Type*} {n : ℕ} (E : α→List Bool) (f : Fin n→α) (xs : List (Fin n)) :
    run (pairBits (encode (List.ofFn (fun i=>E (f i))),encode (xs.map (fun i=>i.val.bits))))=
      encode ((xs.map f).map E) := by
  simp only [run,mapWith_encode,item,extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn,
    List.map_map,Function.comp_def]
end MetricKMedianRecovery.BitMachine.BinaryIndexMap

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic
lemma ranking_injective {r : ℕ} (v : Fin r→ℚ) : Function.Injective (ranking v) := by
  intro i j h
  exact Fin.ext (congrArg (fun p=> (ofLex p).2) h)
lemma rank_value_mono : Monotone (fun p : ℚ ×ₗ ℕ=>((ofLex p).1:ℝ)) := by
  intro x y h
  exact Rat.cast_le.mpr (Prod.Lex.le_iff'.mp h).1
def bottomValues {r : ℕ} (v : Fin r→ℚ) (k : ℕ) : List ℚ :=
  (((Finset.univ.image (ranking v)).sort (·≤·)).take k).map (fun p=>(ofLex p).1)
lemma bottom_sum_cast {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    ((bottomValues v k).sum:ℝ)= Completion.bottomSum k (fun i=>(v i:ℝ)) := by
  classical
  let U:=Finset.univ.image (ranking v)
  let B:=Completion.bottomSet U k
  have hU : U.card=r := by simp [U,Finset.card_image_of_injective _ (ranking_injective v)]
  have hB := Completion.bottomSet_subset U k
  obtain ⟨S,_,hS⟩:=Finset.subset_image_iff.mp hB
  have hc : S.card=min k (Fintype.card (Fin r)) := by
    have he:=Completion.bottomSet_card U k
    rw [←hS,Finset.card_image_of_injective _ (ranking_injective v),hU] at he
    simpa using he
  have he : (∑ p∈B,((ofLex p).1:ℝ))=∑ i∈S,(v i:ℝ) := by
    rw [show B=S.image (ranking v) from hS.symm,Finset.sum_image (ranking_injective v).injOn]
    rfl
  have hn := (U.sort_nodup (·≤·)).sublist (List.take_sublist k (U.sort (·≤·)))
  have hb : ((bottomValues v k).sum:ℝ)=∑ p∈B,((ofLex p).1:ℝ) := by
    rw [Rat.cast_list_sum]
    simp only [bottomValues,List.map_map,Function.comp_def]
    exact (List.sum_toFinset _ hn).symm
  rw [hb]
  apply le_antisymm
  · obtain ⟨Y,hY,eY⟩:=Completion.bottomSum_attained k (fun i=>(v i:ℝ))
    have h := Completion.bottomSet_sum_le (fun p : ℚ ×ₗ ℕ=>((ofLex p).1:ℝ)) rank_value_mono U k
      (Y.image (ranking v)) (Finset.image_subset_image (Finset.subset_univ Y)) (by
        rw [Finset.card_image_of_injective _ (ranking_injective v),hU]
        simpa using hY)
    rw [Finset.sum_image (ranking_injective v).injOn] at h
    exact h.trans_eq eY
  · rw [he]
    exact Completion.bottomSum_le _ hc

noncomputable def sumBottom (x : List Bool) : List Bool :=
  RationalArray.sumWords (mapWith (fun y=>extractPrefix (discardPrefix y)) (pairBits ([],bottom x)))
attribute [local irreducible] mapWith
noncomputable def sumBottom_computes : PolyComputes sumBottom := by
  unfold sumBottom
  exact (((const_computes []).pair bottom_computes).comp
    (mapWith_computes (discardPrefix_computes.comp extractPrefix_computes))).comp RationalArray.sumWords_computes
lemma sumBottom_pack {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    sumBottom (pairBits (k.bits,encode (List.ofFn (fun i=>BinaryRational.encode (v i)))))=
      BinaryRational.encode (bottomValues v k).sum := by
  simp only [sumBottom,bottom_pack,mapWith_encode,List.map_map,Function.comp_def,
    extractPrefix_pairBits,discardPrefix_pairBits,entryBits]
  simpa only [RationalArray.encode,bottomValues,List.map_map,Function.comp_def] using RationalArray.sumWords_encode (bottomValues v k)
lemma sumBottom_correct {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    (BinaryRational.decode (sumBottom (pairBits (k.bits,encode (List.ofFn (fun i=>BinaryRational.encode (v i)))))):ℝ)=
      Completion.bottomSum k (fun i=>(v i:ℝ)) := by
  rw [sumBottom_pack,BinaryRational.decode_encode,bottom_sum_cast]
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
