import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DecisionOps
import OAI.Combinatorics.KMedianRecovery.Machines.CappedFold
import OAI.Combinatorics.KMedianRecovery.Recovery.OrderedMaximum

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalBest
open WordOperations WordList BinaryArithmetic
noncomputable def choose (score : List Bool→List Bool) (x : List Bool) : List Bool :=
  if BinaryRational.decode (score (pairBits (Find.context x,Fold.accum x))) <
      BinaryRational.decode (score (pairBits (Find.context x,Find.item x)))
  then Find.item x else Fold.accum x
noncomputable def choose_computes {score : List Bool→List Bool} (hs : PolyComputes score) : PolyComputes (choose score) := by
  have h := (RatOps.lt (RatOps.ofWords ((Find.context_computes.pair Fold.accum_computes).comp hs))
    (RatOps.ofWords ((Find.context_computes.pair Find.item_computes).comp hs))).cond Find.item_computes Fold.accum_computes
  unfold choose
  simpa only [decide_eq_true_eq,Function.comp_def] using h
lemma choose_pack {A : Type*} (enc : A→List Bool) (score : List Bool→List Bool) (ctx : List Bool)
    (r : A→ℚ) (hr : ∀ a,score (pairBits (ctx,enc a))=BinaryRational.encode (r a)) (a s : A) :
    choose score (pairBits (ctx,pairBits (enc a,enc s)))=enc (if r s<r a then a else s) := by
  simp only [choose,Find.context,Find.item,Fold.accum,Function.comp_apply,extractPrefix_pairBits,
    discardPrefix_pairBits,hr,BinaryRational.decode_encode]
  split_ifs <;> rfl
def pack (ctx seed : List Bool) (ws : List (List Bool)) : List Bool := pairBits (ctx,pairBits (seed,encode ws))
noncomputable def run (score : List Bool→List Bool) (x : List Bool) : List Bool :=
  CappedFold.run (choose score) (pairBits (x,Fold.pack (discardPrefix (discardPrefix x)) (extractPrefix x)
    (extractPrefix (discardPrefix x))))
noncomputable def run_computes {score : List Bool→List Bool} (hs : PolyComputes score) : PolyComputes (run score) :=
  (id_computes.pair (Fold.pack_computes (discardPrefix_computes.comp discardPrefix_computes) extractPrefix_computes
    (discardPrefix_computes.comp extractPrefix_computes))).comp (CappedFold.run_computes (choose_computes hs))
lemma run_pack {A : Type*} (enc : A→List Bool) (score : List Bool→List Bool) (ctx : List Bool)
    (r : A→ℚ) (hr : ∀ a,score (pairBits (ctx,enc a))=BinaryRational.encode (r a)) (s : A) (xs : List A) :
    run score (pack ctx (enc s) (xs.map enc))=enc (OrderedMaximum.run r s xs) := by
  unfold run
  simp only [pack,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [CappedFold.run_typed enc enc (fun s a=>if r s<r a then a else s) (choose score) ctx
    (pairBits (ctx,pairBits (enc s,encode (xs.map enc)))) (fun s a=>choose_pack enc score ctx r hr a s) s xs]
  · rw [OrderedMaximum.fold]
  · intro n
    rw [OrderedMaximum.fold]
    rcases OrderedMaximum.mem r s (xs.take n) with he|he
    · rw [he]
      simp only [pairBits_length]
      omega
    · have hh := WordList.length_member_le_encode (ws:=xs.map enc) (w:=enc (OrderedMaximum.run r s (xs.take n)))
        (List.mem_map.mpr ⟨_,List.mem_of_mem_take he,rfl⟩)
      simp only [pairBits_length]
      omega
noncomputable def fromList (score : List Bool→List Bool) (x : List Bool) : List Bool :=
  run score (pairBits (extractPrefix x,pairBits (head (discardPrefix x),tail (discardPrefix x))))
noncomputable def fromList_computes {score : List Bool→List Bool} (hs : PolyComputes score) : PolyComputes (fromList score) :=
  (extractPrefix_computes.pair ((discardPrefix_computes.comp WordList.head_computes).pair
    (discardPrefix_computes.comp WordList.tail_computes))).comp (run_computes hs)
lemma fromList_pack {A : Type*} (enc : A→List Bool) (score : List Bool→List Bool) (ctx : List Bool)
    (r : A→ℚ) (hr : ∀ a,score (pairBits (ctx,enc a))=BinaryRational.encode (r a)) (xs : List A) (hx : xs≠[]) :
    fromList score (pairBits (ctx,encode (xs.map enc)))=enc (OrderedMaximum.ofList r xs hx) := by
  cases xs with
  | nil=>exact False.elim (hx rfl)
  | cons a as=>
    simp only [fromList,extractPrefix_pairBits,discardPrefix_pairBits,List.map_cons,encode,head_cons,tail_cons]
    exact run_pack enc score ctx r hr a as
end MetricKMedianRecovery.BitMachine.BinaryRationalBest

end OAI
