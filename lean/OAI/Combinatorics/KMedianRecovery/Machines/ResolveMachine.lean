import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LengthCandidates
import OAI.Combinatorics.KMedianRecovery.Recovery.PlanResult
import OAI.Combinatorics.KMedianRecovery.Recovery.CrossEdge

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryResolve
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
def pack {m : ℕ} (base : List Bool) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m)))) (R : CanonicalMergeCrossing.Result (Label (Fin m))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,key.bits,BinaryRational.encode b,k.bits,List.replicate N true,
    setBits B,historyBits P,BinaryCross.resultBits R]
def rf (n : ℕ) : List Bool→List Bool := field n ∘ field 9
noncomputable def rf_computes (n : ℕ) : PolyComputes (rf n) := (field_computes 9).comp (field_computes n)
def bf (n : ℕ) : List Bool→List Bool := field n ∘ field 0
noncomputable def bf_computes (n : ℕ) : PolyComputes (bf n) := (field_computes 0).comp (field_computes n)
def H : List Bool→List Bool := extractPrefix ∘ rf 1
noncomputable def H_computes : PolyComputes H := (rf_computes 1).comp extractPrefix_computes
def T : List Bool→List Bool := discardPrefix ∘ rf 1
noncomputable def T_computes : PolyComputes T := (rf_computes 1).comp discardPrefix_computes
def G : List Bool→List Bool := extractPrefix ∘ rf 2
noncomputable def G_computes : PolyComputes G := (rf_computes 2).comp extractPrefix_computes
def U : List Bool→List Bool := discardPrefix ∘ rf 2
noncomputable def U_computes : PolyComputes U := (rf_computes 2).comp discardPrefix_computes
noncomputable def prefixH (x : List Bool) : List Bool := field 8 x++cons (H x) []
noncomputable def prefixH_computes : PolyComputes prefixH := (field_computes 8).append (cons_computes H_computes (const_computes []))
noncomputable def finishInput (x : List Bool) : List Bool := encode [field 7 x,bf 7 x,prefixH x,T x]
noncomputable def finishInput_computes : PolyComputes finishInput :=
  list_computes [field 7,bf 7,prefixH,T] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨field_computes _⟩
    · exact ⟨bf_computes _⟩
    · exact ⟨prefixH_computes⟩
    · exact ⟨T_computes⟩)
noncomputable def sameInput (x : List Bool) : List Bool := encode [field 7 x,bf 7 x,prefixH x,T x,rf 2 x]
noncomputable def sameInput_computes : PolyComputes sameInput :=
  list_computes [field 7,bf 7,prefixH,T,rf 2] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨field_computes _⟩
    · exact ⟨bf_computes _⟩
    · exact ⟨prefixH_computes⟩
    · exact ⟨T_computes⟩
    · exact ⟨rf_computes _⟩)
noncomputable def fallbackInput (x : List Bool) : List Bool := encode [field 7 x,bf 7 x,field 8 x,[]]
noncomputable def fallbackInput_computes : PolyComputes fallbackInput := cons_computes (field_computes 7)
  (cons_computes (bf_computes 7) (cons_computes (field_computes 8) (cons_computes (const_computes []) (const_computes []))))
noncomputable def viewInput (x : List Bool) : List Bool := encode [bf 2 x,bf 2 x,H x,G x,pairBits (bf 0 x,bf 1 x)]
noncomputable def viewInput_computes : PolyComputes viewInput :=
  list_computes [bf 2,bf 2,H,G,(fun x=>pairBits (bf 0 x,bf 1 x))] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨bf_computes _⟩
    · exact ⟨bf_computes _⟩
    · exact ⟨H_computes⟩
    · exact ⟨G_computes⟩
    · exact ⟨(bf_computes 0).pair (bf_computes 1)⟩)
noncomputable def view : List Bool→List Bool := BinaryLength.view ∘ viewInput
noncomputable def view_computes : PolyComputes view := viewInput_computes.comp BinaryLength.view_computes
noncomputable def plan : List Bool→List Bool := List.tail ∘ view
noncomputable def plan_computes : PolyComputes plan := view_computes.comp WordOperations.tail_computes
noncomputable def sensitiveInput (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,field 2 x,field 3 x,field 4 x,field 5 x,field 6 x,H x,T x,U x,plan x]
noncomputable def sensitiveInput_computes : PolyComputes sensitiveInput :=
  list_computes [field 0,field 1,field 2,field 3,field 4,field 5,field 6,H,T,U,plan] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨field_computes 0⟩
    · exact ⟨field_computes 1⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨field_computes 3⟩
    · exact ⟨field_computes 4⟩
    · exact ⟨field_computes 5⟩
    · exact ⟨field_computes 6⟩
    · exact ⟨H_computes⟩
    · exact ⟨T_computes⟩
    · exact ⟨U_computes⟩
    · exact ⟨plan_computes⟩)
noncomputable def planResultInput (x : List Bool) : List Bool := encode [sensitiveInput x,field 7 x,field 8 x,BinarySensitive.run (sensitiveInput x)]
noncomputable def planResultInput_computes : PolyComputes planResultInput :=
  list_computes [sensitiveInput,field 7,field 8,BinarySensitive.run ∘ sensitiveInput] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨sensitiveInput_computes⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩
    · exact ⟨sensitiveInput_computes.comp BinarySensitive.run_computes⟩)
noncomputable def sensitive (x : List Bool) : List Bool := if view x=[] then
  pairBits ([],BinaryCoupled.finish (fallbackInput x)) else BinaryPlanResult.run (planResultInput x)
noncomputable def sensitive_computes : PolyComputes sensitive := by
  change PolyComputes (fun x=>if view x=[] then pairBits ([],BinaryCoupled.finish (fallbackInput x)) else BinaryPlanResult.run (planResultInput x))
  simpa only [Function.comp_def,decide_eq_true_eq] using (view_computes.comp isEmpty_computes).cond
    ((const_computes []).pair (fallbackInput_computes.comp BinaryCoupled.finish_computes))
    (planResultInput_computes.comp BinaryPlanResult.run_computes)
noncomputable def run (x : List Bool) : List Bool := if value (rf 0 x)=0 then
  pairBits ([],BinaryCoupled.finish (finishInput x)) else if value (rf 0 x)=1 then
  pairBits ([true],BinaryCoupled.same (sameInput x)) else sensitive x
noncomputable def run_computes : PolyComputes run := by
  have h0:=NatOps.eq (rf_computes 0) (const_computes (0:ℕ).bits)
  have h1:=NatOps.eq (rf_computes 0) (const_computes (1:ℕ).bits)
  change PolyComputes (fun x=>if value (rf 0 x)=0 then pairBits ([],BinaryCoupled.finish (finishInput x)) else
    if value (rf 0 x)=1 then pairBits ([true],BinaryCoupled.same (sameInput x)) else sensitive x)
  simpa only [value_bits,decide_eq_true_eq,Function.comp_def] using h0.cond
    ((const_computes []).pair (finishInput_computes.comp BinaryCoupled.finish_computes))
    (h1.cond ((const_computes [true]).pair (sameInput_computes.comp BinaryCoupled.same_computes)) sensitive_computes)
lemma view_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m))
    (Q B : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (P : List (List (Label (Fin m)))) (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    view (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q v z lam) n q key b k N B P (.sensitive H G T U))=
      Find.optionEncode ((CanonicalLengthView.view (rows distance) (F.image original) ((F.sort (·≤·)).map original) H G).map BinaryLength.planBits) := by
  unfold view viewInput
  simp only [BinaryResolve.H,BinaryResolve.G,bf,rf,Function.comp_apply,pack,BinaryCross.resultBits,BinaryCross.nodeBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,
    BinaryFiniteContext.pack]
  change BinaryLength.view (BinaryLength.ctxBits distance (F.image original) (BinaryLabel.orderedSort (F.image original)) H G)=_
  rw [←BinaryFiniteContext.originalSort]
  exact BinaryLength.view_pack ..
lemma run_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m))
    (B : Finset (Label (Fin m))) (v z lam M : ℚ) (n q key N precision k : ℕ)
    (P : List (List (Label (Fin m)))) (R : CanonicalMergeCrossing.Result (Label (Fin m))) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) (PhaseHistoryTransfer.after ∅ P) v z lam)
      n q key (20*N*M) k precision B P R)=
      BinaryCoupled.outcomeBits (CanonicalCoupledMerge.resolve loc distance F v M N precision q n k key B lam P R) := by
  let base:=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) (PhaseHistoryTransfer.after ∅ P) v z lam
  change run (pack base n q key (20*N*M) k precision B P R)=_
  cases R with
  | success H T=>
    simp only [run,rf,Function.comp_apply,pack,BinaryCross.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,ite_true]
    simp only [finishInput,prefixH,bf,rf,BinaryResolve.H,BinaryResolve.T,Function.comp_apply,base,BinaryFiniteContext.pack,
      BinaryCross.nodeBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits]
    rw [show historyBits P++cons (labels H) []=historyBits (P++[H]) by rw [BinaryCoupled.historyBits_append,BinaryCoupled.historyBits_cons]; rfl]
    rw [BinaryCoupled.finish_pack]
    rfl
  | common H T U=>
    simp only [run,rf,Function.comp_apply,pack,BinaryCross.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,one_ne_zero,ite_false,ite_true]
    simp only [sameInput,prefixH,bf,rf,BinaryResolve.H,BinaryResolve.T,Function.comp_apply,base,BinaryFiniteContext.pack,
      BinaryCross.nodeBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits]
    rw [show historyBits P++cons (labels H) []=historyBits (P++[H]) by rw [BinaryCoupled.historyBits_append,BinaryCoupled.historyBits_cons]; rfl]
    rw [BinaryCoupled.same_pack]
    rfl
  | sensitive H G T U=>
    have hv:=view_pack distance loc F (PhaseHistoryTransfer.after ∅ P) B v z lam n q key (20*N*M) k precision P H G T U
    change view (pack base n q key (20*N*M) k precision B P (.sensitive H G T U))=_ at hv
    simp only [run,rf,Function.comp_apply,pack,BinaryCross.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,show (2:ℕ)≠0 by omega,show (2:ℕ)≠1 by omega,ite_false]
    change sensitive (pack base n q key (20*N*M) k precision B P (.sensitive H G T U))=_
    unfold sensitive
    rw [hv]
    cases he : CanonicalLengthView.view (rows distance) (F.image original) ((F.sort (·≤·)).map original) H G with
    | none=>
      simp only [Option.map_none,Find.optionEncode,ite_true]
      simp only [fallbackInput,bf,Function.comp_apply,pack,base,BinaryFiniteContext.pack,
        field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      change pairBits ([],BinaryCoupled.finish (encode [setBits B,BinaryRational.encode lam,historyBits P,historyBits (m:=m) []]))=_
      rw [BinaryCoupled.finish_pack]
      simp only [CanonicalCoupledMerge.resolve,he]
      rfl
    | some J=>
      simp only [Option.map_some,Find.optionEncode,List.cons_ne_nil,ite_false]
      have hs : sensitiveInput (pack base n q key (20*N*M) k precision B P (.sensitive H G T U))=
          BinarySensitive.pack base n q key (20*N*M) k precision H T U J := by
        unfold sensitiveInput plan
        simp only [Function.comp_apply]
        rw [hv]
        simp only [he,Option.map_some,Find.optionEncode,List.tail_cons,BinaryResolve.H,BinaryResolve.T,BinaryResolve.U,rf,Function.comp_apply,
          pack,BinaryCross.resultBits,BinaryCross.nodeBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
          extractPrefix_pairBits,discardPrefix_pairBits,BinarySensitive.pack]
      unfold planResultInput
      rw [hs,BinarySensitive.run_pack]
      simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      change BinaryPlanResult.run (BinaryPlanResult.pack (BinarySensitive.pack base n q key (20*N*M) k precision H T U J) B P
        (CanonicalSensitiveEndpoint.run loc distance F (PhaseHistoryTransfer.after ∅ P) v lam (20*N*M) q n k key precision H T U J))=_
      rw [BinaryPlanResult.run_pack]
      simp only [CanonicalCoupledMerge.resolve,he]
      generalize CanonicalSensitiveEndpoint.run loc distance F (PhaseHistoryTransfer.after ∅ P) v lam (20*N*M) q n k key precision H T U J=R
      cases R <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryResolve

end OAI
