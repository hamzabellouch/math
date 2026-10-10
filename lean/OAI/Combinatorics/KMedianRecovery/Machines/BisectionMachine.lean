import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.NatWords
import OAI.Combinatorics.KMedianRecovery.Machines.GridMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBisection
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
lemma clog_two_eq_size_pred (n : ℕ) : Nat.clog 2 n=Nat.size (n-1) := by
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.clog_le_iff_le_pow (by decide : 1<2),Nat.size_le]
  have hp : 0<2^k := by positivity
  omega
noncomputable def predWords (x : List Bool) : List Bool := (value x-1).bits
noncomputable def predWords_computes : PolyComputes predWords := by
  change PolyComputes (fun x=>(value x-1).bits)
  simpa only [value_bits,id_eq] using NatOps.sub id_computes (const_computes (1:ℕ).bits)
noncomputable def logWord (x : List Bool) : List Bool := RepeatedAppend.copies (predWords x).length [true]
noncomputable def logWord_computes : PolyComputes logWord := UnaryResources.copy_computes predWords_computes (const_computes [true])
lemma logWord_eq (x : List Bool) : logWord x=List.replicate (Nat.clog 2 (value x)) true := by
  unfold logWord predWords
  rw [show [true]=List.replicate 1 true from rfl,UnaryResources.copies_replicate,Nat.mul_one,
    Nat.size_eq_bits_len,clog_two_eq_size_pred]
noncomputable def width (x : List Bool) : ℚ := BinaryRational.decode (field 4 x)-BinaryRational.decode (field 3 x)
noncomputable def width_computes : PolyComputes (fun x=>BinaryRational.encode (width x)) :=
  RatOps.sub (RatOps.ofWords (field_computes 4)) (RatOps.ofWords (field_computes 3))
noncomputable def widthCeil (x : List Bool) : List Bool := (Nat.ceil (width x)).bits
noncomputable def widthCeil_computes : PolyComputes widthCeil := RatOps.natCeil width_computes
noncomputable def fuel (x : List Bool) : List Bool := field 0 x++logWord (widthCeil x)
noncomputable def fuel_computes : PolyComputes fuel := (field_computes 0).append (widthCeil_computes.comp logWord_computes)
noncomputable def context (x : List Bool) : List Bool := encode [field 1 x,field 2 x,field 3 x,field 4 x]
noncomputable def context_computes : PolyComputes context := list_computes [field 1,field 2,field 3,field 4] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> exact ⟨field_computes _⟩)
noncomputable def input (x : List Bool) : List Bool := pairBits (fuel x,context x)
noncomputable def input_computes : PolyComputes input := fuel_computes.pair context_computes
noncomputable def run (query : List Bool→List Bool) : List Bool→List Bool := BinaryGrid.run query ∘ input
noncomputable def run_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (run query) :=
  input_computes.comp (BinaryGrid.run_computes hq)
def pack (N : ℕ) (ctx : List Bool) (k : ℕ) (a b : ℚ) : List Bool :=
  encode [List.replicate N true,ctx,k.bits,BinaryRational.encode a,BinaryRational.encode b]
lemma fuel_pack (N : ℕ) (ctx : List Bool) (k : ℕ) (a b : ℚ) :
    fuel (pack N ctx k a b)=List.replicate (PriceBisection.iterations a b N) true := by
  simp only [fuel,pack,widthCeil,width,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryRational.decode_encode,logWord_eq,value_bits,←List.replicate_add,PriceBisection.iterations]
lemma context_pack (N : ℕ) (ctx : List Bool) (k : ℕ) (a b : ℚ) :
    context (pack N ctx k a b)=encode [ctx,k.bits,BinaryRational.encode a,BinaryRational.encode b] := by
  simp only [context,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma run_pack (query : List Bool→List Bool) (N : ℕ) (ctx : List Bool) (k : ℕ) (a b : ℚ) :
    run query (pack N ctx k a b)=
      let f:=fun s=>value (query (pairBits (ctx,BinaryRational.encode s)))
      let I:=PriceBisection.search f k (PriceBisection.iterations a b N) (a,b)
      pairBits (BinaryRational.encode I.1,BinaryRational.encode I.2) := by
  have hc : BinaryGrid.count query (encode [ctx,k.bits,BinaryRational.encode a,BinaryRational.encode b])=
      (fun s=>value (query (pairBits (ctx,BinaryRational.encode s)))) := by
    funext s
    simp only [BinaryGrid.count,field_encode,List.getElem?_cons_zero,Option.getD_some]
  simp only [run,Function.comp_apply,input,fuel_pack,context_pack,BinaryGrid.run_pack,List.length_replicate,
    hc,BinaryGrid.boundK,BinaryGrid.lower,BinaryGrid.upper,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,BinaryRational.decode_encode]
end MetricKMedianRecovery.BitMachine.BinaryBisection

end OAI
