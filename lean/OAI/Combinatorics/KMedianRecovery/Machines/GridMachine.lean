import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Op2
import OAI.Combinatorics.KMedianRecovery.Recovery.DyadicGrid

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGrid
open WordOperations WordList BinaryArithmetic DyadicGrid
open BinaryOpeningPayment (field field_computes field_encode)
def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
def gf (n : ℕ) : List Bool → List Bool := field n ∘ discardPrefix
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def gf_computes (n : ℕ) : PolyComputes (gf n) := discardPrefix_computes.comp (field_computes n)
def num : List Bool → List Bool := extractPrefix ∘ discardPrefix
def den : List Bool → List Bool := discardPrefix ∘ discardPrefix
noncomputable def num_computes : PolyComputes num := discardPrefix_computes.comp extractPrefix_computes
noncomputable def den_computes : PolyComputes den := discardPrefix_computes.comp discardPrefix_computes
noncomputable def pointWords (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (cf 2 x)+(BinaryRational.decode (cf 3 x)-BinaryRational.decode (cf 2 x))*
    (value (num x):ℚ)/(value (den x):ℚ))
noncomputable def pointWords_computes : PolyComputes pointWords :=
  RatOps.add (RatOps.ofWords (cf_computes 2))
    (RatOps.div (RatOps.mul (RatOps.sub (RatOps.ofWords (cf_computes 3)) (RatOps.ofWords (cf_computes 2)))
      (RatOps.nat num_computes)) (RatOps.nat den_computes))
lemma pointWords_pack (ctx : List Bool) (i d : ℕ) :
    pointWords (pairBits (ctx,pairBits (i.bits,d.bits)))=BinaryRational.encode
      (point (BinaryRational.decode (field 2 ctx)) (BinaryRational.decode (field 3 ctx)) i d) := by
  simp only [pointWords,cf,num,den,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,point]
noncomputable def doubled (n : ℕ) (x : List Bool) : List Bool := (2*value (gf n x)).bits
noncomputable def doubled_computes (n : ℕ) : PolyComputes (doubled n) := by
  change PolyComputes (fun x => (2*value (gf n x)).bits)
  simpa only [value_bits] using NatOps.mul (const_computes (2:ℕ).bits) (gf_computes n)
noncomputable def summed (x : List Bool) : List Bool := (value (gf 0 x)+value (gf 1 x)).bits
noncomputable def summed_computes : PolyComputes summed := NatOps.add (gf_computes 0) (gf_computes 1)
noncomputable def midpoint (x : List Bool) : List Bool := pointWords (pairBits (extractPrefix x,pairBits (summed x,doubled 2 x)))
noncomputable def midpoint_computes : PolyComputes midpoint :=
  (extractPrefix_computes.pair (summed_computes.pair (doubled_computes 2))).comp pointWords_computes
noncomputable def queryInput (x : List Bool) : List Bool := pairBits (cf 0 x,midpoint x)
noncomputable def queryInput_computes : PolyComputes queryInput := (cf_computes 0).pair midpoint_computes
noncomputable def chooseLeft (query : List Bool→List Bool) (x : List Bool) : Bool :=
  decide (value (cf 1 x)≤value (query (queryInput x)))
noncomputable def chooseLeft_computes {query : List Bool→List Bool} (hq : PolyComputes query) :
    PolyComputes (fun x=>[chooseLeft query x]) := NatOps.le (cf_computes 1) (queryInput_computes.comp hq)
noncomputable def upLeft (x : List Bool) : List Bool := encode [summed x,doubled 1 x,doubled 2 x]
noncomputable def upRight (x : List Bool) : List Bool := encode [doubled 0 x,summed x,doubled 2 x]
noncomputable def upLeft_computes : PolyComputes upLeft := list_computes [summed,doubled 1,doubled 2] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨summed_computes⟩
  · exact ⟨doubled_computes _⟩
  · exact ⟨doubled_computes _⟩)
noncomputable def upRight_computes : PolyComputes upRight := list_computes [doubled 0,summed,doubled 2] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨doubled_computes _⟩
  · exact ⟨summed_computes⟩
  · exact ⟨doubled_computes _⟩)
noncomputable def step (query : List Bool→List Bool) (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,if chooseLeft query x then upLeft x else upRight x)
noncomputable def step_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (step query) :=
  extractPrefix_computes.pair ((chooseLeft_computes hq).cond upLeft_computes upRight_computes)
def stateBits (ctx : List Bool) (g : State) : List Bool := pairBits (ctx,encode [g.1.bits,g.2.1.bits,g.2.2.bits])
def count (query : List Bool→List Bool) (ctx : List Bool) (s : ℚ) : ℕ :=
  value (query (pairBits (field 0 ctx,BinaryRational.encode s)))
def boundK (ctx : List Bool) : ℕ := value (field 1 ctx)
def lower (ctx : List Bool) : ℚ := BinaryRational.decode (field 2 ctx)
def upper (ctx : List Bool) : ℚ := BinaryRational.decode (field 3 ctx)
lemma step_pack (query : List Bool→List Bool) (ctx : List Bool) (g : State) :
    step query (stateBits ctx g)=stateBits ctx (advance (count query ctx) (boundK ctx) (lower ctx) (upper ctx) g) := by
  rcases g with ⟨i,j,d⟩
  simp only [step,chooseLeft,queryInput,midpoint,summed,doubled,cf,gf,stateBits,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,value_bits,pointWords_pack,advance,count,boundK,lower,upper,decide_eq_true_eq]
  split_ifs with h <;> simp [upLeft,upRight,summed,doubled,gf,Function.comp_apply,
    discardPrefix_pairBits,field_encode,value_bits,h]
lemma iterate_pack (query : List Bool→List Bool) (ctx : List Bool) (n : ℕ) :
    (step query)^[n] (stateBits ctx start)=stateBits ctx
      ((advance (count query ctx) (boundK ctx) (lower ctx) (upper ctx))^[n] start) := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [Function.iterate_succ_apply',ih,step_pack,Function.iterate_succ_apply']
lemma bits_of_le_pow {i n : ℕ} (hi : i≤2^n) : i.bits.length≤n+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hp : 0<2^n := by positivity
  rw [pow_succ]
  omega
lemma iterate_length (query : List Bool→List Bool) (ctx : List Bool) (n : ℕ) :
    ((step query)^[n] (stateBits ctx start)).length≤2*ctx.length+6*n+13 := by
  rw [iterate_pack]
  obtain ⟨hl,hu,hd⟩:=iterate_bounds (count query ctx) (boundK ctx) (lower ctx) (upper ctx) n
  have h1:=bits_of_le_pow hl
  have h2:=bits_of_le_pow hu
  have h3:=bits_of_le_pow hd.le
  simp only [stateBits,pairBits_length,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil]
  omega
noncomputable def capacity : PolynomialCounter (10*Polynomial.X+20) := PolynomialCounter.choose _
noncomputable def initial (x : List Bool) : List Bool := stateBits (discardPrefix x) start
noncomputable def initial_computes : PolyComputes initial := discardPrefix_computes.pair (const_computes (encode ([0,1,1].map Nat.bits)))
noncomputable def runInput (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (capacity.word x,initial x))
noncomputable def runInput_computes : PolyComputes runInput := extractPrefix_computes.pair (capacity.computes.pair initial_computes)
noncomputable def stateRun (query : List Bool→List Bool) : List Bool→List Bool := BoundedIteration.run (step query) ∘ runInput
noncomputable def stateRun_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (stateRun query) :=
  runInput_computes.comp (BoundedIteration.run_computes (step_computes hq))
lemma stateRun_pack (query : List Bool→List Bool) (fuel ctx : List Bool) :
    stateRun query (pairBits (fuel,ctx))=(step query)^[fuel.length] (stateBits ctx start) := by
  simp only [stateRun,Function.comp_apply,runInput,initial,extractPrefix_pairBits,discardPrefix_pairBits]
  apply BoundedIteration.run_eq
  intro j hj
  have hh:=iterate_length query ctx j
  rw [capacity.word_length]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,pairBits_length]
  omega
noncomputable def endpoint (n : ℕ) (x : List Bool) : List Bool := pointWords (pairBits (extractPrefix x,pairBits (gf n x,gf 2 x)))
noncomputable def endpoint_computes (n : ℕ) : PolyComputes (endpoint n) :=
  (extractPrefix_computes.pair ((gf_computes n).pair (gf_computes 2))).comp pointWords_computes
noncomputable def finish (x : List Bool) : List Bool := pairBits (endpoint 0 x,endpoint 1 x)
noncomputable def finish_computes : PolyComputes finish := (endpoint_computes 0).pair (endpoint_computes 1)
lemma finish_pack (ctx : List Bool) (g : State) : finish (stateBits ctx g)=
    pairBits (BinaryRational.encode (interval (lower ctx) (upper ctx) g).1,
      BinaryRational.encode (interval (lower ctx) (upper ctx) g).2) := by
  rcases g with ⟨i,j,d⟩
  simp only [finish,endpoint,gf,Function.comp_apply,stateBits,extractPrefix_pairBits,discardPrefix_pairBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,pointWords_pack,interval,lower,upper]
noncomputable def run (query : List Bool→List Bool) : List Bool→List Bool := finish ∘ stateRun query
noncomputable def run_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (run query) :=
  (stateRun_computes hq).comp finish_computes
lemma run_pack (query : List Bool→List Bool) (fuel ctx : List Bool) :
    run query (pairBits (fuel,ctx))=
      let I:=PriceBisection.search (count query ctx) (boundK ctx) fuel.length (lower ctx,upper ctx)
      pairBits (BinaryRational.encode I.1,BinaryRational.encode I.2) := by
  simp only [run,Function.comp_apply,stateRun_pack,iterate_pack,finish_pack,iterate_interval]
end MetricKMedianRecovery.BitMachine.BinaryGrid

end OAI
