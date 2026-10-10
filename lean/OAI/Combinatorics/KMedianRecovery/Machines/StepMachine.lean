import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.ScanMachine
import OAI.Combinatorics.KMedianRecovery.Machines.ResolveMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledStep
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
def pack {m : ℕ} (base : List Bool) (n q : ℕ) (b : ℚ) (precision k : ℕ) (s : State (Fin m)) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,BinaryRational.encode b,List.replicate precision true,k.bits,stateBits s]
def sf (i : ℕ) : List Bool→List Bool := field i ∘ field 6
noncomputable def sf_computes (i : ℕ) : PolyComputes (sf i) := (field_computes 6).comp (field_computes i)
def bf (i : ℕ) : List Bool→List Bool := field i ∘ field 0
noncomputable def bf_computes (i : ℕ) : PolyComputes (bf i) := (field_computes 0).comp (field_computes i)
noncomputable def mappedFree (x : List Bool) : List Bool := BinaryCoupled.mapFree (field 6 x)
noncomputable def mappedFree_computes : PolyComputes mappedFree :=
  (field_computes 6).comp (BinaryCoupled.mapFree_computes)
noncomputable def mappedPrefix (x : List Bool) : List Bool := BinaryCoupled.mapPrefix (field 6 x)
noncomputable def mappedPrefix_computes : PolyComputes mappedPrefix := by
  unfold mappedPrefix
  simpa only [Function.comp_def] using
    (field_computes 6).comp BinaryCoupled.mapPrefix_computes
noncomputable def Q (x : List Bool) : List Bool := BinaryFiniteMachine.after (pairBits ([],mappedPrefix x))
noncomputable def Q_computes : PolyComputes Q :=
  ((const_computes []).pair mappedPrefix_computes).comp BinaryFiniteMachine.after_computes
noncomputable def power (x : List Bool) : List Bool := BinaryPhaseCount.power (pairBits (field 2 x,bf 5 x))
noncomputable def power_computes : PolyComputes power := by
  unfold power
  simpa only [Function.comp_def] using
    ((field_computes 2).pair (bf_computes 5)).comp BinaryPhaseCount.power_computes
noncomputable def base (x : List Bool) : List Bool := encode [bf 0 x,bf 1 x,bf 2 x,Q x,bf 4 x,bf 5 x,power x,sf 4 x]
noncomputable def base_computes : PolyComputes base :=
  list_computes [bf 0,bf 1,bf 2,Q,bf 4,bf 5,power,sf 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨bf_computes 0⟩
    · exact ⟨bf_computes 1⟩
    · exact ⟨bf_computes 2⟩
    · exact ⟨Q_computes⟩
    · exact ⟨bf_computes 4⟩
    · exact ⟨bf_computes 5⟩
    · exact ⟨power_computes⟩
    · exact ⟨sf_computes 4⟩
)
noncomputable def H (x : List Bool) : List Bool := WordList.head (sf 5 x)
noncomputable def H_computes : PolyComputes H :=
  (sf_computes 5).comp (WordList.head_computes)
noncomputable def T (x : List Bool) : List Bool := WordList.tail (sf 5 x)
noncomputable def T_computes : PolyComputes T :=
  (sf_computes 5).comp (WordList.tail_computes)
noncomputable def G (x : List Bool) : List Bool := WordList.head (sf 6 x)
noncomputable def G_computes : PolyComputes G :=
  (sf_computes 6).comp (WordList.head_computes)
noncomputable def U (x : List Bool) : List Bool := WordList.tail (sf 6 x)
noncomputable def U_computes : PolyComputes U :=
  (sf_computes 6).comp (WordList.tail_computes)
noncomputable def QG (x : List Bool) : List Bool := BinaryFiniteContext.union (pairBits (Q x,G x))
noncomputable def QG_computes : PolyComputes QG :=
  (Q_computes.pair G_computes).comp BinaryFiniteContext.union_computes
noncomputable def contBase (x : List Bool) : List Bool := encode [bf 0 x,bf 1 x,bf 2 x,QG x,bf 4 x,bf 5 x,power x,sf 4 x]
noncomputable def contBase_computes : PolyComputes contBase :=
  list_computes [bf 0,bf 1,bf 2,QG,bf 4,bf 5,power,sf 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨bf_computes 0⟩
    · exact ⟨bf_computes 1⟩
    · exact ⟨bf_computes 2⟩
    · exact ⟨QG_computes⟩
    · exact ⟨bf_computes 4⟩
    · exact ⟨bf_computes 5⟩
    · exact ⟨power_computes⟩
    · exact ⟨sf_computes 4⟩
)
noncomputable def W (x : List Bool) : List Bool := BinaryFiniteMachine.continuation (pairBits (field 1 x,pairBits (true::field 2 x,contBase x)))
noncomputable def W_computes : PolyComputes W := by
  unfold W
  simpa only [Function.comp_def,List.cons_append,List.nil_append] using
    ((field_computes 1).pair (((const_computes [true]).append (field_computes 2)).pair contBase_computes)).comp BinaryFiniteMachine.continuation_computes
noncomputable def ctx (x : List Bool) : List Bool := encode [bf 2 x,Q x,field 5 x]
noncomputable def ctx_computes : PolyComputes ctx :=
  list_computes [bf 2,Q,field 5] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨bf_computes 2⟩
    · exact ⟨Q_computes⟩
    · exact ⟨field_computes 5⟩
)
noncomputable def c (x : List Bool) : List Bool := BinaryCross.finalCount (pairBits (ctx x,pairBits (G x,W x)))
noncomputable def c_computes : PolyComputes c :=
  (ctx_computes.pair (G_computes.pair W_computes)).comp BinaryCross.finalCount_computes
noncomputable def a (x : List Bool) : List Bool := BinaryFiniteContext.countInter (pairBits (BinaryFiniteMachine.after (pairBits (Q x,sf 5 x)),bf 2 x))
noncomputable def a_computes : PolyComputes a :=
  (((Q_computes.pair (sf_computes 5)).comp BinaryFiniteMachine.after_computes).pair (bf_computes 2)).comp BinaryFiniteContext.countInter_computes
noncomputable def qbits (x : List Bool) : List Bool := (field 2 x).length.bits
noncomputable def qbits_computes : PolyComputes qbits :=
  by
  change PolyComputes (fun x=>(field 2 x).length.bits)
  simpa only [Function.comp_def,UnaryResources.lengthBits_eq] using (field_computes 2).comp UnaryResources.lengthBits_computes
noncomputable def key (x : List Bool) : List Bool := (3*value (qbits x)).bits
noncomputable def key_computes : PolyComputes key :=
  by
  change PolyComputes (fun x=>(3*value (qbits x)).bits)
  simpa only [value_bits] using NatOps.mul (const_computes (3:ℕ).bits) qbits_computes
noncomputable def spare (x : List Bool) : List Bool := (value (key x)+1).bits
noncomputable def spare_computes : PolyComputes spare :=
  by
  change PolyComputes (fun x=>(value (key x)+1).bits)
  simpa only [value_bits] using NatOps.add key_computes (const_computes (1:ℕ).bits)
noncomputable def leafKey (x : List Bool) : List Bool := (value (key x)+2).bits
noncomputable def leafKey_computes : PolyComputes leafKey :=
  by
  change PolyComputes (fun x=>(value (key x)+2).bits)
  simpa only [value_bits] using NatOps.add key_computes (const_computes (2:ℕ).bits)
noncomputable def crossInput (x : List Bool) : List Bool := encode [base x,key x,spare x,field 5 x,field 1 x,field 2 x,H x,G x,T x,W x]
noncomputable def crossInput_computes : PolyComputes crossInput :=
  list_computes [base,key,spare,field 5,field 1,field 2,H,G,T,W] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨base_computes⟩
    · exact ⟨key_computes⟩
    · exact ⟨spare_computes⟩
    · exact ⟨field_computes 5⟩
    · exact ⟨field_computes 1⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨H_computes⟩
    · exact ⟨G_computes⟩
    · exact ⟨T_computes⟩
    · exact ⟨W_computes⟩
)
noncomputable def bankInput (x : List Bool) : List Bool := encode [bf 2 x,mappedFree x,qbits x]
noncomputable def bankInput_computes : PolyComputes bankInput :=
  list_computes [bf 2,mappedFree,qbits] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨bf_computes 2⟩
    · exact ⟨mappedFree_computes⟩
    · exact ⟨qbits_computes⟩
)
noncomputable def banks (x : List Bool) : List Bool := BinaryFiniteContext.banks (bankInput x)
noncomputable def banks_computes : PolyComputes banks :=
  bankInput_computes.comp BinaryFiniteContext.banks_computes
noncomputable def resolveInput (x : List Bool) : List Bool := encode [base x,field 1 x,field 2 x,leafKey x,field 3 x,field 5 x,field 4 x,banks x,mappedPrefix x,(BinaryFiniteCross.run ∘ crossInput) x]
noncomputable def resolveInput_computes : PolyComputes resolveInput :=
  list_computes [base,field 1,field 2,leafKey,field 3,field 5,field 4,banks,mappedPrefix,(BinaryFiniteCross.run ∘ crossInput)] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨base_computes⟩
    · exact ⟨field_computes 1⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨leafKey_computes⟩
    · exact ⟨field_computes 3⟩
    · exact ⟨field_computes 5⟩
    · exact ⟨field_computes 4⟩
    · exact ⟨banks_computes⟩
    · exact ⟨mappedPrefix_computes⟩
    · exact ⟨crossInput_computes.comp BinaryFiniteCross.run_computes⟩
)
noncomputable def prefixG (x : List Bool) : List Bool := mappedPrefix x++cons (G x) []
noncomputable def prefixG_computes : PolyComputes prefixG :=
  mappedPrefix_computes.append (cons_computes G_computes (const_computes []))
noncomputable def finishInput (x : List Bool) : List Bool := encode [mappedFree x,sf 4 x,prefixG x,W x]
noncomputable def finishInput_computes : PolyComputes finishInput :=
  list_computes [mappedFree,sf 4,prefixG,W] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨mappedFree_computes⟩
    · exact ⟨sf_computes 4⟩
    · exact ⟨prefixG_computes⟩
    · exact ⟨W_computes⟩
)
noncomputable def advanceInput (x : List Bool) : List Bool := encode [field 6 x,G x,W x,U x]
noncomputable def advanceInput_computes : PolyComputes advanceInput :=
  list_computes [field 6,G,W,U] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨field_computes 6⟩
    · exact ⟨G_computes⟩
    · exact ⟨W_computes⟩
    · exact ⟨U_computes⟩
)
noncomputable def fallbackInput (x : List Bool) : List Bool := encode [sf 0 x,sf 3 x,sf 1 x,(fun _=>[]) x]
noncomputable def fallbackInput_computes : PolyComputes fallbackInput :=
  list_computes [sf 0,sf 3,sf 1,(fun _=>[])] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨sf_computes 0⟩
    · exact ⟨sf_computes 3⟩
    · exact ⟨sf_computes 1⟩
    · exact ⟨const_computes []⟩
)
noncomputable def sandwiched (x : List Bool) : Bool := (decide (value (a x)<value (field 5 x)) && decide (value (field 5 x)<value (c x))) ||
  (decide (value (c x)<value (field 5 x)) && decide (value (field 5 x)<value (a x)))
noncomputable def sandwiched_computes : PolyComputes (fun x=>[sandwiched x]) :=
  ((NatOps.lt a_computes (field_computes 5)).and (NatOps.lt (field_computes 5) c_computes)).or
    ((NatOps.lt c_computes (field_computes 5)).and (NatOps.lt (field_computes 5) a_computes))
noncomputable def active (x : List Bool) : List Bool := if decide (value (c x)=value (field 5 x)) then pairBits ([],BinaryCoupled.finish (finishInput x))
  else if sandwiched x then BinaryResolve.run (resolveInput x) else pairBits ([true],BinaryCoupled.advance (advanceInput x))
noncomputable def active_computes : PolyComputes active := by
  unfold active
  simpa only [Function.comp_def] using
    (NatOps.eq c_computes (field_computes 5)).cond
      ((const_computes []).pair (finishInput_computes.comp BinaryCoupled.finish_computes))
      (sandwiched_computes.cond (resolveInput_computes.comp BinaryResolve.run_computes)
        ((const_computes [true]).pair (advanceInput_computes.comp BinaryCoupled.advance_computes)))
noncomputable def nonempty (x : List Bool) : Bool := (!(decide (sf 5 x=[]))) && (!(decide (sf 6 x=[])))
noncomputable def nonempty_computes : PolyComputes (fun x=>[nonempty x]) :=
  ((sf_computes 5).comp isEmpty_computes).not.and (((sf_computes 6).comp isEmpty_computes).not)
noncomputable def run (x : List Bool) : List Bool := if nonempty x then active x else pairBits ([],BinaryCoupled.finish (fallbackInput x))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using
    nonempty_computes.cond active_computes ((const_computes []).pair (fallbackInput_computes.comp BinaryCoupled.finish_computes))
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
