import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.BoundedDecision

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations
noncomputable def RepeatedAppend.fixed_computes (n : ℕ) : PolyComputes (RepeatedAppend.copies n) := by
  induction n with
  | zero => exact const_computes []
  | succ n ih => exact ih.append id_computes
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.BitMachine.WordList.CappedFold
open WordOperations
noncomputable def run (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  Fold.accum (BoundedIteration.run (Fold.step f)
    (pairBits (Count.run (Fold.items (discardPrefix x)),
      pairBits (RepeatedAppend.copies 4 x,discardPrefix x))))
noncomputable def run_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (run f) :=
  ((((discardPrefix_computes.comp Fold.items_computes).comp Count.run_computes).pair
    ((RepeatedAppend.fixed_computes 4).pair discardPrefix_computes)).comp
      (BoundedIteration.run_computes (Fold.step_computes hf))).comp Fold.accum_computes
lemma run_pack (f : List Bool → List Bool) (cap ctx a : List Bool) (ws : List (List Bool))
    (hB : ∀ n, ((ws.take n).foldl (Fold.operation f ctx) a).length≤cap.length) :
    run f (pairBits (cap,Fold.pack (encode ws) ctx a))=ws.foldl (Fold.operation f ctx) a := by
  unfold run
  rw [discardPrefix_pairBits,Fold.items_pack,Count.run_encode,BoundedIteration.run_eq]
  · simp only [List.length_replicate,Fold.iterate_pack,Fold.accum_pack,List.take_length]
  · intro j _
    rw [Fold.iterate_pack,Fold.length_pack,RepeatedAppend.length_copies,pairBits_length,Fold.length_pack]
    dsimp only at *
    have hws:=length_encode_drop ws j
    have hb:=hB j
    omega

lemma fold_encode {S A : Type*} (encS : S → List Bool) (encA : A → List Bool)
    (g : S → A → S) (f : List Bool → List Bool) (ctx : List Bool)
    (hf : ∀ s a,f (pairBits (ctx,pairBits (encA a,encS s)))=encS (g s a))
    (s : S) (xs : List A) :
    (xs.map encA).foldl (Fold.operation f ctx) (encS s)=encS (xs.foldl g s) := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>
    simp only [List.map_cons,List.foldl_cons,Fold.operation,hf]
    exact ih (g s a)
lemma run_typed {S A : Type*} (encS : S → List Bool) (encA : A → List Bool)
    (g : S → A → S) (f : List Bool → List Bool) (ctx cap : List Bool)
    (hf : ∀ s a,f (pairBits (ctx,pairBits (encA a,encS s)))=encS (g s a))
    (s : S) (xs : List A) (hB : ∀ n,(encS ((xs.take n).foldl g s)).length≤cap.length) :
    run f (pairBits (cap,Fold.pack (encode (xs.map encA)) ctx (encS s)))=encS (xs.foldl g s) := by
  rw [run_pack]
  · exact fold_encode encS encA g f ctx hf s xs
  · intro n
    rw [←List.map_take,fold_encode encS encA g f ctx hf]
    exact hB n
end MetricKMedianRecovery.BitMachine.WordList.CappedFold

end OAI
