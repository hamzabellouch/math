import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FinishPhase
import OAI.Combinatorics.KMedianRecovery.Recovery.FiniteContext
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelLookup

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (pack labels)

noncomputable def initial (x : List Bool) : List Bool := BinaryPhaseCount.start
  (pairBits (BinaryFiniteContext.run x,field 6 x))
noncomputable def initial_computes : PolyComputes initial :=
  (BinaryFiniteContext.run_computes.pair (field_computes 6)).comp BinaryPhaseCount.start_computes
lemma initial_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    initial (pack distance loc F Q v z lam)=BinaryPhaseUpdate.stateBits
      (FiniteLabelContinuation.rows loc F Q (rows distance)) (FiniteLabelContinuation.select loc F Q F)
      v lam ⟨FiniteLabelContinuation.select loc F Q Q,z,Vector.replicate d 0⟩ := by
  rw [initial,BinaryFiniteContext.run_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryPhaseCount.start_pack]

noncomputable def finished : List Bool → List Bool := BinaryRunTrace.finished ∘ initial
noncomputable def finished_computes : PolyComputes finished :=
  PolyComputes.comp (f:=initial) (g:=BinaryRunTrace.finished) initial_computes BinaryRunTrace.finished_computes
noncomputable def completedTrace : List Bool → List Bool := discardPrefix ∘ finished
noncomputable def completed_trace_computes : PolyComputes completedTrace :=
  PolyComputes.comp (f:=finished) (g:=discardPrefix) finished_computes discardPrefix_computes
noncomputable def completed : List Bool → List Bool := WordList.map extractPrefix ∘ completedTrace
noncomputable def completed_computes : PolyComputes completed :=
  PolyComputes.comp (f:=completedTrace) (g:=WordList.map extractPrefix)
    completed_trace_computes (map_computes extractPrefix_computes)
lemma completed_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    completed (pack distance loc F Q v z lam)=BinaryOpeningActivity.indices
      (RationalPhase.completion (FiniteLabelContinuation.rows loc F Q (rows distance))
        (FiniteLabelContinuation.select loc F Q F) v z lam (FiniteLabelContinuation.select loc F Q Q)) := by
  simp only [completed,completedTrace,finished,Function.comp_apply,initial_pack,BinaryRunTrace.finished_pack,BinaryPhaseTrace.pack,discardPrefix_pairBits,
    map_encode,BinaryOpeningActivity.indices,RationalPhase.completion,List.map_map,Function.comp_def,
    BinaryPhaseFirst.eventBits,extractPrefix_pairBits]
noncomputable def complete (x : List Bool) : List Bool :=
  BinaryLabelLookup.run (pairBits (BinaryFiniteContext.alphabet x,completed x))
noncomputable def complete_computes : PolyComputes complete := by
  have completeComputes :=
    (BinaryFiniteContext.alphabet_computes.pair completed_computes).comp BinaryLabelLookup.run_computes
  unfold complete
  simpa only [Function.comp_def] using completeComputes
lemma complete_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    complete (pack distance loc F Q v z lam)=
      labels (FiniteLabelContinuation.complete loc (rows distance) F v z lam Q) := by
  rw [complete,BinaryFiniteContext.alphabet_pack,completed_pack]
  rw [labels,BinaryLabelLookup.run_pack]
  rfl

noncomputable def data : List Bool → List Bool := discardPrefix ∘ discardPrefix
noncomputable def data_computes : PolyComputes data := discardPrefix_computes.comp discardPrefix_computes
noncomputable def phase (x : List Bool) : List Bool :=
  BinaryPhaseCount.power (pairBits (extractPrefix (discardPrefix x),field 5 (data x)))
noncomputable def phase_computes : PolyComputes phase := by
  have phaseComputes :=
    ((discardPrefix_computes.comp extractPrefix_computes).pair (data_computes.comp (field_computes 5))).comp
      BinaryPhaseCount.power_computes
  unfold phase
  simpa only [Function.comp_def] using phaseComputes
noncomputable def start (x : List Bool) : List Bool := BinaryPhaseCount.start
  (pairBits (BinaryFiniteContext.run (data x),phase x))
noncomputable def start_computes : PolyComputes start :=
  ((data_computes.comp BinaryFiniteContext.run_computes).pair phase_computes).comp BinaryPhaseCount.start_computes
lemma start_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (q n : ℕ) :
    start (pairBits (List.replicate n true,pairBits (List.replicate q true,pack distance loc F Q v z lam)))=
      BinaryPhaseUpdate.stateBits (FiniteLabelContinuation.rows loc F Q (rows distance))
        (FiniteLabelContinuation.select loc F Q F) v lam
        ⟨FiniteLabelContinuation.select loc F Q Q,(1+v^2)^q,Vector.replicate d 0⟩ := by
  simp only [start,phase,data,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,BinaryFiniteContext.run_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryPhaseCount.power_pack,BinaryPhaseCount.start_pack]

def historyBits {m : ℕ} (hs : List (List (Label (Fin m)))) : List Bool := encode (hs.map labels)
noncomputable def history (x : List Bool) : List Bool :=
  discardPrefix (BinaryHistoryRun.run (pairBits (extractPrefix x,start x)))
noncomputable def history_computes : PolyComputes history :=
  ((extractPrefix_computes.pair start_computes).comp BinaryHistoryRun.run_computes).comp discardPrefix_computes
noncomputable def continuation (x : List Bool) : List Bool := BinaryLabelLookup.history
  (pairBits (BinaryFiniteContext.alphabet (data x),history x))
noncomputable def continuation_computes : PolyComputes continuation := by
  have continuationComputes :=
    ((data_computes.comp BinaryFiniteContext.alphabet_computes).pair history_computes).comp
      BinaryLabelLookup.history_computes
  unfold continuation
  simpa only [Function.comp_def] using continuationComputes
lemma continuation_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (q n : ℕ) :
    continuation (pairBits (List.replicate n true,pairBits (List.replicate q true,pack distance loc F Q v z lam)))=
      historyBits (FiniteLabelContinuation.continuation loc (rows distance) F v lam q n Q) := by
  simp only [continuation,history,data,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryFiniteContext.alphabet_pack,start_pack,BinaryHistoryRun.run_pack,BinaryHistoryRun.pack]
  rw [labels,BinaryLabelLookup.history_pack]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves
noncomputable def copied (x : List Bool) : List Bool :=
  if value (levelWords (discardPrefix x))=0 then
    pairBits ((value (extractPrefix x)+1).bits,pairBits (parentWords (discardPrefix x),BinaryRational.encode 0))
  else discardPrefix x
noncomputable def copied_computes : PolyComputes copied := by
  have hi : PolyComputes (fun x=>(value (extractPrefix x)+1).bits) := by
    simpa only [value_bits] using NatOps.add extractPrefix_computes (const_computes (1:ℕ).bits)
  have ht:=hi.pair ((discardPrefix_computes.comp parentWords_computes).pair (const_computes (BinaryRational.encode 0)))
  have hh := (NatOps.zero (discardPrefix_computes.comp levelWords_computes)).cond ht discardPrefix_computes
  unfold copied
  simpa only [Function.comp_def,decide_eq_true_eq] using hh
lemma copied_pack {m : ℕ} (key : ℕ) (x : Label (Fin m)) :
    copied (pairBits (key.bits,encode x))=encode (copy key x) := by
  simp only [copied,extractPrefix_pairBits,discardPrefix_pairBits,levelWords_encode,value_bits,parentWords_encode]
  cases x with
  | inl i=>rfl
  | inr c=>simp only [level,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,copy,Sum.elim_inr]

noncomputable def swapped (x : List Bool) : List Bool :=
  if eq (pairBits (discardPrefix x,extractPrefix (extractPrefix x))) then discardPrefix (extractPrefix x)
  else if eq (pairBits (discardPrefix x,discardPrefix (extractPrefix x))) then extractPrefix (extractPrefix x)
  else discardPrefix x
noncomputable def swapped_computes : PolyComputes swapped :=
  ((discardPrefix_computes.pair (extractPrefix_computes.comp extractPrefix_computes)).comp eq_computes).cond
    (extractPrefix_computes.comp discardPrefix_computes)
    (((discardPrefix_computes.pair (extractPrefix_computes.comp discardPrefix_computes)).comp eq_computes).cond
      (extractPrefix_computes.comp extractPrefix_computes) discardPrefix_computes)
lemma swapped_pack {m : ℕ} (a b x : Label (Fin m)) :
    swapped (pairBits (pairBits (encode a,encode b),encode x))=encode (Equiv.swap a b x) := by
  simp only [swapped,extractPrefix_pairBits,discardPrefix_pairBits,eq_pair,decide_eq_true_eq,Equiv.swap_apply_def]
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
lemma labels_append {m : ℕ} (xs ys : List (Label (Fin m))) : labels (xs++ys)=labels xs++labels ys := by
  simp only [labels,List.map_append,encode_append]
lemma labels_cons {m : ℕ} (x : Label (Fin m)) (xs : List (Label (Fin m))) :
    labels (x::xs)=WordList.cons (BinaryLabel.encode x) (labels xs) := rfl
lemma labels_nil {m : ℕ} : labels ([] : List (Label (Fin m)))=[] := rfl

noncomputable def union (x : List Bool) : List Bool := BinaryLabel.sort (extractPrefix x++discardPrefix x)
noncomputable def union_computes : PolyComputes union :=
  (extractPrefix_computes.append discardPrefix_computes).comp BinaryLabel.sort_computes
lemma union_pack {m : ℕ} (S T : Finset (Label (Fin m))) :
    union (pairBits (setBits S,setBits T))=setBits (S∪T) := by
  simp only [union,extractPrefix_pairBits,discardPrefix_pairBits,setBits,labels,←encode_append,
    ←List.map_append,BinaryLabel.sort_encode,List.toFinset_append,BinaryLabel.orderedSort,Finset.sort_toFinset]
lemma union_list_pack {m : ℕ} (S : Finset (Label (Fin m))) (xs : List (Label (Fin m))) :
    union (pairBits (setBits S,labels xs))=setBits (S∪xs.toFinset) := by
  simp only [union,extractPrefix_pairBits,discardPrefix_pairBits,setBits,labels,←encode_append,
    ←List.map_append,BinaryLabel.sort_encode,List.toFinset_append,BinaryLabel.orderedSort,Finset.sort_toFinset]
noncomputable def replaceOpen (x : List Bool) : List Bool :=
  encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),discardPrefix x,
    field 4 (extractPrefix x),field 5 (extractPrefix x),field 6 (extractPrefix x),field 7 (extractPrefix x)]
noncomputable def replaceOpen_computes : PolyComputes replaceOpen :=
  list_computes [field 0 ∘ extractPrefix,field 1 ∘ extractPrefix,field 2 ∘ extractPrefix,discardPrefix,
    field 4 ∘ extractPrefix,field 5 ∘ extractPrefix,field 6 ∘ extractPrefix,field 7 ∘ extractPrefix] (by
    intro f hf
    refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨extractPrefix_computes.comp (field_computes _)⟩ | exact ⟨discardPrefix_computes⟩)
lemma replaceOpen_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q R : Finset (Label (Fin m))) (v z lam : ℚ) :
    replaceOpen (pairBits (pack distance loc F Q v z lam,setBits R))=pack distance loc F R v z lam := by
  simp only [replaceOpen,extractPrefix_pairBits,discardPrefix_pairBits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves PhaseSequence
open BinaryFiniteContext (labels setBits)
lemma historyBits_append {m : ℕ} (hs gs : List (List (Label (Fin m)))) :
    historyBits (hs++gs)=historyBits hs++historyBits gs := by
  simp only [historyBits,List.map_append,encode_append]
lemma historyBits_cons {m : ℕ} (H : List (Label (Fin m))) (hs : List (List (Label (Fin m)))) :
    historyBits (H::hs)=WordList.cons (labels H) (historyBits hs) := rfl
lemma historyBits_nil {m : ℕ} : historyBits ([] : List (List (Label (Fin m))))=[] := rfl
lemma flatten_historyBits {m : ℕ} (hs : List (List (Label (Fin m)))) :
    Flatten.run (historyBits hs)=labels hs.flatten := by
  rw [historyBits,Flatten.run_encode]
  induction hs with
  | nil=>rfl
  | cons H hs ih=>simp only [List.map_cons,List.flatten_cons,ih,BinaryFiniteContext.labels_append]
noncomputable def after (x : List Bool) : List Bool :=
  BinaryLabel.sort (extractPrefix x++Flatten.run (discardPrefix x))
noncomputable def after_computes : PolyComputes after :=
  (extractPrefix_computes.append (discardPrefix_computes.comp Flatten.run_computes)).comp BinaryLabel.sort_computes
lemma after_pack {m : ℕ} (Q : Finset (Label (Fin m))) (hs : List (List (Label (Fin m)))) :
    after (pairBits (setBits Q,historyBits hs))=setBits (PhaseHistoryTransfer.after Q hs) := by
  simp only [after,extractPrefix_pairBits,discardPrefix_pairBits,flatten_historyBits]
  have hh:=BinaryFiniteContext.union_list_pack Q hs.flatten
  simp only [BinaryFiniteContext.union,extractPrefix_pairBits,discardPrefix_pairBits] at hh
  rw [hh]
  congr 1
  clear hh
  induction hs generalizing Q with
  | nil=>simp only [List.flatten_nil,List.toFinset_nil,Finset.union_empty,PhaseHistoryTransfer.after]
  | cons H hs ih=>simpa only [List.flatten_cons,List.toFinset_append,←Finset.union_assoc,PhaseHistoryTransfer.after] using ih (Q∪H.toFinset)
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

end OAI
