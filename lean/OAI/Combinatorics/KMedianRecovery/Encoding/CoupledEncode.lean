import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.FiniteMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCorrection
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
def encode {m : ℕ} : Correction (Fin m) → List Bool
  | .identity => []
  | .shorten key i l u => pairBits (BinaryLabel.encode (leaf key i u),BinaryLabel.encode (leaf key i l))
noncomputable def applyWord (x : List Bool) : List Bool :=
  if extractPrefix x=[] then discardPrefix x else BinaryLabel.swapped x
noncomputable def applyWord_computes : PolyComputes applyWord :=
  by
  change PolyComputes (fun x=>if extractPrefix x=[] then discardPrefix x else BinaryLabel.swapped x)
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (extractPrefix_computes.comp isEmpty_computes).cond discardPrefix_computes BinaryLabel.swapped_computes
lemma applyWord_pack {m : ℕ} (c : Correction (Fin m)) (a : Label (Fin m)) :
    applyWord (pairBits (encode c,BinaryLabel.encode a))=BinaryLabel.encode (c.apply a) := by
  cases c with
  | identity=>rfl
  | shorten key i l u=>
    unfold applyWord encode
    simp only [extractPrefix_pairBits]
    rw [ite_eq_right (by intro he; have hh:=congrArg List.length he; simp only [pairBits_length,List.length_nil] at hh; omega)]
    exact BinaryLabel.swapped_pack _ _ _
noncomputable def mapRow : List Bool→List Bool := mapWith applyWord
noncomputable def mapRow_computes : PolyComputes mapRow := mapWith_computes applyWord_computes
lemma mapRow_pack {m : ℕ} (c : Correction (Fin m)) (H : List (Label (Fin m))) :
    mapRow (pairBits (encode c,labels H))=labels (H.map c.apply) := by
  simp only [mapRow,labels,mapWith_encode,List.map_map,Function.comp_def,applyWord_pack]
noncomputable def mapHistory : List Bool→List Bool := mapWith mapRow
noncomputable def mapHistory_computes : PolyComputes mapHistory := mapWith_computes mapRow_computes
lemma mapHistory_pack {m : ℕ} (c : Correction (Fin m)) (H : List (List (Label (Fin m)))) :
    mapHistory (pairBits (encode c,historyBits H))=historyBits (H.map (List.map c.apply)) := by
  simp only [mapHistory,historyBits,mapWith_encode,List.map_map,Function.comp_def,mapRow_pack]
noncomputable def mapSet : List Bool→List Bool := BinaryLabel.sort ∘ mapRow
noncomputable def mapSet_computes : PolyComputes mapSet := mapRow_computes.comp BinaryLabel.sort_computes
lemma mapSet_pack {m : ℕ} (c : Correction (Fin m)) (S : Finset (Label (Fin m))) :
    mapSet (pairBits (encode c,setBits S))=setBits (S.image c.apply) := by
  unfold mapSet
  change BinaryLabel.sort (mapRow (pairBits (encode c,labels (BinaryLabel.orderedSort S))))=_
  rw [mapRow_pack]
  unfold labels
  rw [BinaryLabel.sort_encode]
  apply congrArg (fun S : Finset (Label (Fin m))=>WordList.encode ((BinaryLabel.orderedSort S).map BinaryLabel.encode))
  ext a
  simp only [List.mem_toFinset,List.mem_map,BinaryLabel.orderedSort,Finset.mem_sort,Finset.mem_image]
end MetricKMedianRecovery.BitMachine.BinaryCorrection

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
def stateBits {m : ℕ} (s : State (Fin m)) : List Bool :=
  encode [setBits s.B,historyBits s.P,BinaryCorrection.encode s.correction,
    BinaryRational.encode s.lam,BinaryRational.encode s.lam',historyBits s.T,historyBits s.U]
def outputBits {m : ℕ} (o : Output (Fin m)) : List Bool := encode [setBits o.B,BinaryRational.encode o.lam,historyBits o.P]
def outcomeBits {m : ℕ} : Outcome (Fin m)→List Bool
 | .inl o=>pairBits ([],outputBits o)
 | .inr s=>pairBits ([true],stateBits s)
noncomputable def mapFree (x : List Bool) : List Bool := BinaryCorrection.mapSet (pairBits (field 2 x,field 0 x))
noncomputable def mapFree_computes : PolyComputes mapFree := ((field_computes 2).pair (field_computes 0)).comp BinaryCorrection.mapSet_computes
lemma mapFree_pack {m : ℕ} (s : State (Fin m)) : mapFree (stateBits s)=setBits s.mapFree := by
  simp only [mapFree,stateBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryCorrection.mapSet_pack,State.mapFree]
noncomputable def mapPrefix (x : List Bool) : List Bool := BinaryCorrection.mapHistory (pairBits (field 2 x,field 1 x))
attribute [local irreducible] BinaryCorrection.mapHistory
noncomputable def mapPrefix_computes : PolyComputes mapPrefix := by
  unfold mapPrefix
  exact ((field_computes 2).pair (field_computes 1)).comp BinaryCorrection.mapHistory_computes
lemma mapPrefix_pack {m : ℕ} (s : State (Fin m)) : mapPrefix (stateBits s)=historyBits s.mapPrefix := by
  simp only [mapPrefix,stateBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryCorrection.mapHistory_pack,State.mapPrefix]
lemma historyBits_append {m : ℕ} (P T : List (List (Label (Fin m)))) : historyBits (P++T)=historyBits P++historyBits T := by
  simp only [historyBits,List.map_append,encode_append]
lemma historyBits_cons {m : ℕ} (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
    historyBits (H::T)=cons (labels H) (historyBits T) := rfl
noncomputable def finish (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 2 x++field 3 x]
noncomputable def finish_computes : PolyComputes finish := cons_computes (field_computes 0)
  (cons_computes (field_computes 1) (cons_computes ((field_computes 2).append (field_computes 3)) (const_computes [])))
lemma finish_pack {m : ℕ} (B : Finset (Label (Fin m))) (lam : ℚ) (P T : List (List (Label (Fin m)))) :
    finish (encode [setBits B,BinaryRational.encode lam,historyBits P,historyBits T])=
      outputBits (CanonicalCoupledMerge.finish B lam P T) := by
  simp only [finish,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    outputBits,CanonicalCoupledMerge.finish,historyBits_append]
noncomputable def same (x : List Bool) : List Bool := encode [field 0 x,field 2 x,[],field 1 x,field 1 x,field 3 x,field 4 x]
noncomputable def same_computes : PolyComputes same := list_computes [field 0,field 2,(fun _=>[]),field 1,field 1,field 3,field 4] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact ⟨field_computes _⟩ | exact ⟨const_computes _⟩)
lemma same_pack {m : ℕ} (B : Finset (Label (Fin m))) (lam : ℚ) (P T U : List (List (Label (Fin m)))) :
    same (encode [setBits B,BinaryRational.encode lam,historyBits P,historyBits T,historyBits U])=
      stateBits (sameState B lam P T U) := by
  simp only [same,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    stateBits,sameState,BinaryCorrection.encode]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
