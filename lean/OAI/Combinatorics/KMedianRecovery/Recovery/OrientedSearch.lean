import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LengthSearch
import OAI.Combinatorics.KMedianRecovery.Recovery.DecisionOps
import OAI.Combinatorics.KMedianRecovery.Machines.BisectionMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOrientedSearch
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def reversedInput (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),
  BinaryRational.encode (BinaryRational.decode (discardPrefix (extractPrefix x))-BinaryRational.decode (discardPrefix x)))
noncomputable def reversedInput_computes : PolyComputes reversedInput :=
  (extractPrefix_computes.comp extractPrefix_computes).pair
    (RatOps.sub (RatOps.ofWords (extractPrefix_computes.comp discardPrefix_computes)) (RatOps.ofWords discardPrefix_computes))
noncomputable def reversed (query : List Bool→List Bool) : List Bool→List Bool := query ∘ reversedInput
noncomputable def reversed_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (reversed query) :=
  reversedInput_computes.comp hq
lemma reversed_pack (query : List Bool→List Bool) (ctx : List Bool) (b s : ℚ) :
    reversed query (pairBits (pairBits (ctx,BinaryRational.encode b),BinaryRational.encode s))=
      query (pairBits (ctx,BinaryRational.encode (b-s))) := by
  simp only [reversed,Function.comp_apply,reversedInput,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode]
noncomputable def reverseContext (x : List Bool) : List Bool := pairBits (field 1 x,field 4 x)
noncomputable def reverseContext_computes : PolyComputes reverseContext := (field_computes 1).pair (field_computes 4)
noncomputable def reverseInput (x : List Bool) : List Bool := encode
  [field 0 x,reverseContext x,field 2 x,field 3 x,field 4 x]
noncomputable def reverseInput_computes : PolyComputes reverseInput :=
  list_computes [field 0,reverseContext,field 2,field 3,field 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨field_computes _⟩ | exact ⟨reverseContext_computes⟩)
lemma reverseInput_pack (N : ℕ) (ctx : List Bool) (k : ℕ) (b : ℚ) :
    reverseInput (BinaryBisection.pack N ctx k 0 b)=
      BinaryBisection.pack N (pairBits (ctx,BinaryRational.encode b)) k 0 b := by
  simp only [reverseInput,reverseContext,BinaryBisection.pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
noncomputable def reflect (x : List Bool) : List Bool := pairBits
  (BinaryRational.encode (BinaryRational.decode (extractPrefix x)-BinaryRational.decode (discardPrefix (discardPrefix x))),
   BinaryRational.encode (BinaryRational.decode (extractPrefix x)-BinaryRational.decode (extractPrefix (discardPrefix x))))
noncomputable def reflect_computes : PolyComputes reflect :=
  (RatOps.sub (RatOps.ofWords extractPrefix_computes) (RatOps.ofWords (discardPrefix_computes.comp discardPrefix_computes))).pair
    (RatOps.sub (RatOps.ofWords extractPrefix_computes) (RatOps.ofWords (discardPrefix_computes.comp extractPrefix_computes)))
lemma reflect_pack (b l u : ℚ) : reflect (pairBits (BinaryRational.encode b,
    pairBits (BinaryRational.encode l,BinaryRational.encode u)))=
    pairBits (BinaryRational.encode (b-u),BinaryRational.encode (b-l)) := by
  simp only [reflect,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode]
noncomputable def reverseRun (query : List Bool→List Bool) (x : List Bool) : List Bool :=
  reflect (pairBits (field 4 x,BinaryBisection.run (reversed query) (reverseInput x)))
noncomputable def reverseRun_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (reverseRun query) :=
  ((field_computes 4).pair (reverseInput_computes.comp (BinaryBisection.run_computes (reversed_computes hq)))).comp reflect_computes
lemma reverseRun_pack (query : List Bool→List Bool) (N : ℕ) (ctx : List Bool) (k : ℕ) (b : ℚ) :
    reverseRun query (BinaryBisection.pack N ctx k 0 b)=
      let I:=PriceBisection.search (fun s=>value (query (pairBits (ctx,BinaryRational.encode (b-s))))) k
        (PriceBisection.iterations 0 b N) (0,b)
      pairBits (BinaryRational.encode (b-I.2),BinaryRational.encode (b-I.1)) := by
  unfold reverseRun
  rw [reverseInput_pack,BinaryBisection.run_pack]
  simp only [reversed_pack,BinaryBisection.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    reflect_pack]
noncomputable def isReversed (query : List Bool→List Bool) (x : List Bool) : Bool :=
  decide (value (query (pairBits (field 1 x,BinaryRational.encode 0)))<value (field 2 x))
noncomputable def isReversed_computes {query : List Bool→List Bool} (hq : PolyComputes query) :
    PolyComputes (fun x=>[isReversed query x]) :=
  NatOps.lt (((field_computes 1).pair (const_computes (BinaryRational.encode 0))).comp hq) (field_computes 2)
noncomputable def run (query : List Bool→List Bool) (x : List Bool) : List Bool :=
  if isReversed query x then reverseRun query x else BinaryBisection.run query x
noncomputable def run_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (run query) :=
  (isReversed_computes hq).cond (reverseRun_computes hq) (BinaryBisection.run_computes hq)
lemma run_pack (query : List Bool→List Bool) (N : ℕ) (ctx : List Bool) (k : ℕ) (b : ℚ) :
    run query (BinaryBisection.pack N ctx k 0 b)=
      let I:=CanonicalLengthSearch.range (fun s=>value (query (pairBits (ctx,BinaryRational.encode s)))) k N b
      pairBits (BinaryRational.encode I.1,BinaryRational.encode I.2) := by
  unfold run
  rw [reverseRun_pack,BinaryBisection.run_pack]
  simp only [isReversed,BinaryBisection.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    value_bits,decide_eq_true_eq,CanonicalLengthSearch.range]
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryOrientedSearch

end OAI
