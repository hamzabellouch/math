import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerUpdateParts
import OAI.Combinatorics.KMedianRecovery.Branching.CopyGround

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
lemma filter_sort {n : ℕ} (F : Finset (Fin n)) (p : Fin n→Prop) [DecidablePred p] :
    (F.sort (·≤·)).filter (fun v=>decide (p v))=(F.filter p).sort (·≤·) := by
  have hn := (Finset.sort_nodup F (·≤·)).filter (fun v=>decide (p v))
  have hp := (Finset.pairwise_sort F (·≤·)).filter (fun v=>decide (p v))
  have hh := (List.toFinset_sort (r:=(·≤·)) hn).mpr hp
  simpa only [List.toFinset_filter,Finset.sort_toFinset,decide_eq_true_eq] using hh.symm
end MetricKMedianRecovery.BitMachine.BinaryFinSet
namespace MetricKMedianRecovery.BitMachine.BinaryBranchBalls
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n a : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (F : Finset (Fin n)) (w : Fin a→Fin n) (R : Fin a→ℚ) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode F,encode (List.ofFn (fun i=>BinarySamplingReference.leafBits (w i) (R i)))]
noncomputable def row (x : List Bool) : List Bool := Lookup.run (pairBits
  (extractPrefix (discardPrefix x),field 0 (extractPrefix x)))
noncomputable def row_computes : PolyComputes row :=
  ((discardPrefix_computes.comp extractPrefix_computes).pair (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes
noncomputable def input (x : List Bool) : List Bool := pairBits
  (pairBits (row x,discardPrefix (discardPrefix x)),field 1 (extractPrefix x))
noncomputable def input_computes : PolyComputes input :=
  (row_computes.pair (discardPrefix_computes.comp discardPrefix_computes)).pair (extractPrefix_computes.comp (field_computes 1))
noncomputable def ball : List Bool→List Bool := filterWith BinarySampler.Update.within ∘ input
noncomputable def ball_computes : PolyComputes ball := input_computes.comp (filterWith_computes BinarySampler.Update.within_computes)
lemma ball_pair (δ : Fin n→Fin n→ℚ) (F : Finset (Fin n)) (w : Fin a→Fin n) (R : Fin a→ℚ) (v : Fin n) (r : ℚ) :
    ball (pairBits (pack δ F w R,BinarySamplingReference.leafBits v r))=BinaryFinSet.encode (F.filter (fun f=>δ v f≤r)) := by
  simp only [ball,Function.comp_apply,input,row,pack,extractPrefix_pairBits,discardPrefix_pairBits,
    BinarySamplingReference.leafBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    extractPrefix_pairBits,discardPrefix_pairBits,RationalMatrix.encode,lookup_ofFn,BinaryFinSet.encode_eq,
    filterWith_encode,List.filter_map,Function.comp_def,BinarySampler.Update.within_pair,BinaryFinSet.filter_sort]
noncomputable def balls (x : List Bool) : List Bool := mapWith ball (pairBits (x,field 2 x))
noncomputable def balls_computes : PolyComputes balls := by
  have ballsComputes := (id_computes.pair (field_computes 2)).comp (mapWith_computes ball_computes)
  unfold balls
  simpa only [Function.comp_def, id_eq] using ballsComputes
lemma balls_pack (δ : Fin n→Fin n→ℚ) (F : Finset (Fin n)) (w : Fin a→Fin n) (R : Fin a→ℚ) :
    balls (pack δ F w R)=encode (List.ofFn (fun i=>BinaryFinSet.encode (F.filter (fun f=>δ (w i) f≤R i)))) := by
  unfold balls
  rw [show field 2 (pack δ F w R)=encode (List.ofFn (fun i=>BinarySamplingReference.leafBits (w i) (R i))) by simp [pack,field_encode]]
  simp only [mapWith_ofFn,ball_pair]
noncomputable def run (x : List Bool) : List Bool := encode [Count.run (field 0 x),balls x]
noncomputable def run_computes : PolyComputes run := cons_computes ((field_computes 0).comp Count.run_computes)
  (cons_computes balls_computes (const_computes []))
lemma run_pack (δ : Fin n→Fin n→ℚ) (F : Finset (Fin n)) (w : Fin a→Fin n) (R : Fin a→ℚ) :
    run (pack δ F w R)=BinaryCopyTables.pack (fun i=>F.filter (fun f=>δ (w i) f≤R i)) := by
  rw [run,balls_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,Option.getD_some,RationalMatrix.encode,Count.run_encode,List.length_ofFn,BinaryCopyTables.pack]
end MetricKMedianRecovery.BitMachine.BinaryBranchBalls

end OAI
