import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RawSlices

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryParser
open WordOperations UnaryTake

def step (x : List Bool) : List Bool :=
  if (data x).head?.getD false then pack true (true::counter x) (data x).tail []
  else pack false (counter x) (data x).tail []
noncomputable def step_computes : PolyComputes step := by
  have ht:=pack_computes true ((const_computes [true]).append counter_computes)
    (data_computes.comp tail_computes) (const_computes [])
  have hf:=pack_computes false counter_computes (data_computes.comp tail_computes) (const_computes [])
  unfold step
  simpa only [Function.comp_def,List.singleton_append] using
    (data_computes.comp head_computes).cond ht hf
def next := While.next step
noncomputable def next_computes : PolyComputes next := by
  have h:=head_computes.cond step_computes id_computes
  convert h using 1
  funext x
  simp only [next,While.next,id_eq]
  cases x with
  | nil=>rfl
  | cons b xs=>cases b <;> rfl
lemma mass_next (x : List Bool) : mass (next x) ≤ mass x := by
  unfold next While.next
  split_ifs
  · unfold step
    cases hd : data x with
    | nil=>simp only [List.head?_nil,Option.getD_none,Bool.false_eq_true,ite_false,mass,counter_pack,
        data_pack,output_pack,List.tail_nil,List.length_nil,hd]; omega
    | cons b d=>cases b <;>
      simp only [List.head?_cons,Option.getD_some,Bool.false_eq_true,ite_false,ite_true,mass,
        counter_pack,data_pack,output_pack,List.tail_cons,List.length_nil,List.length_cons,hd] <;> omega
  · exact le_rfl
lemma length_next (x : List Bool) : (next x).length ≤ max x.length (2*mass (next x)+3) := by
  unfold next While.next
  split_ifs
  · unfold step
    split_ifs <;> simp only [length_pack,mass,counter_pack,data_pack,output_pack,List.length_nil] <;> omega
  · exact Nat.le_max_left _ _
lemma iterate_bounds (x : List Bool) (n : ℕ) :
    mass (next^[n] x)≤ mass x ∧ (next^[n] x).length≤ max x.length (2*mass x+3) := by
  induction n with
  | zero=>exact ⟨le_rfl,Nat.le_max_left _ _⟩
  | succ n ih=>
    rw [Function.iterate_succ_apply']
    have hm:=mass_next (next^[n] x)
    have hl:=length_next (next^[n] x)
    exact ⟨hm.trans ih.1,by omega⟩
def loop (x : List Bool) : List Bool := next^[x.length] x
noncomputable def loop_computes : PolyComputes loop := by
  have h:=BoundedIteration.polynomialRun_computes next_computes Polynomial.X (7*Polynomial.X+3)
  have he (x : List Bool) : BoundedIteration.polynomialRun next Polynomial.X (7*Polynomial.X+3) x=loop x := by
    have ht:=BoundedIteration.polynomialRun_eq next Polynomial.X (7*Polynomial.X+3) x (by
      intro j _
      have hb:=(iterate_bounds x j).2
      obtain ⟨hc,hd,ho⟩:=projection_bounds x
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
      unfold mass at hb
      omega)
    simpa only [Polynomial.eval_X,loop] using ht
  convert h using 1
  funext x
  exact (he x).symm
lemma next_stop (c d : List Bool) : next (pack false c d [])=pack false c d [] := by
  simp only [next,While.next,head_pack,Option.some.injEq,Bool.false_eq_true,ite_false]
lemma next_false (c d : List Bool) : next (pack true c (false::d) [])=pack false c d [] := by
  simp only [next,While.next,head_pack,ite_true,step,data_pack,counter_pack,List.head?_cons,
    Option.getD_some,Bool.false_eq_true,ite_false,List.tail_cons]
lemma next_true (c d : List Bool) : next (pack true c (true::d) [])=pack true (true::c) d [] := by
  simp only [next,While.next,head_pack,ite_true,step,data_pack,counter_pack,List.head?_cons,
    Option.getD_some,List.tail_cons]
lemma exact_prefix (n : ℕ) (c d : List Bool) :
    next^[n+1] (pack true c (List.replicate n true++false::d) [])=
      pack false (List.replicate n true++c) d [] := by
  induction n generalizing c with
  | zero=>simp only [Nat.zero_add,List.replicate_zero,List.nil_append,Function.iterate_one,next_false]
  | succ n ih=>
    rw [List.replicate_succ,List.cons_append,Function.iterate_succ_apply,next_true,ih]
    rw [show List.replicate n true++true::c=(List.replicate (n+1) true)++c by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]]
    simp only [List.replicate_succ,List.cons_append]
noncomputable def run (x : List Bool) : List Bool :=
  let y:=loop (pack true [] x [])
  pairBits (counter y,data y)
noncomputable def run_computes : PolyComputes run :=
  ((pack_computes true (const_computes []) id_computes (const_computes [])).comp loop_computes).comp
    (counter_computes.pair data_computes)
lemma run_code (n : ℕ) (d : List Bool) :
    run (List.replicate n true++false::d)=pairBits (List.replicate n true,d) := by
  dsimp only [run,loop]
  have hl : n+1≤(pack true [] (List.replicate n true++false::d) []).length := by
    simp only [length_pack,List.length_nil,List.length_append,List.length_replicate,List.length_cons]; omega
  rw [show (pack true [] (List.replicate n true++false::d) []).length=
    (pack true [] (List.replicate n true++false::d) []).length-(n+1)+(n+1) by omega]
  rw [Function.iterate_add_apply,exact_prefix,List.append_nil,Function.iterate_fixed (next_stop _ _),
    counter_pack,data_pack]
end MetricKMedianRecovery.BitMachine.UnaryParser

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser
open WordOperations
attribute [local irreducible] UnaryParser.run UnaryTake.takeWords UnaryTake.dropWords
noncomputable def nat (x : List Bool) : List Bool :=
  pairBits (UnaryTake.takeWords (UnaryParser.run x),UnaryTake.dropWords (UnaryParser.run x))
noncomputable def nat_computes : PolyComputes nat :=
  UnaryParser.run_computes.comp (UnaryTake.takeWords_computes.pair UnaryTake.dropWords_computes)
lemma nat_code (n : ℕ) (tail : List Bool) :
    nat (RationalMetricInput.natBits n++tail)=pairBits (n.bits,tail) := by
  simp only [RationalMetricInput.natBits,List.append_assoc,List.cons_append,List.nil_append,nat,
    UnaryParser.run_code,UnaryTake.takeWords,UnaryTake.dropWords,extractPrefix_pairBits,
    discardPrefix_pairBits,List.length_replicate,List.take_left,List.drop_left]
attribute [local irreducible] nat
noncomputable def numerator (x : List Bool) : List Bool :=
  x.head?.getD false::extractPrefix (nat x.tail)
noncomputable def numerator_computes : PolyComputes numerator :=
  head_computes.append ((tail_computes.comp nat_computes).comp extractPrefix_computes)
noncomputable def denominator (x : List Bool) : List Bool := nat (discardPrefix (nat x.tail))
noncomputable def denominator_computes : PolyComputes denominator :=
  ((tail_computes.comp nat_computes).comp discardPrefix_computes).comp nat_computes
attribute [local irreducible] numerator denominator
noncomputable def rational (x : List Bool) : List Bool :=
  pairBits (pairBits (numerator x,extractPrefix (denominator x)),discardPrefix (denominator x))
noncomputable def rational_computes : PolyComputes rational :=
  (numerator_computes.pair (denominator_computes.comp extractPrefix_computes)).pair
    (denominator_computes.comp discardPrefix_computes)
lemma rational_code (r : ℚ) (tail : List Bool) :
    rational (RationalMetricInput.rationalBits r++tail)=pairBits (BinaryRational.encode r,tail) := by
  have hs : decide (r<0)=decide (r.num<0) := by
    apply decide_eq_decide.mpr
    rw [lt_iff_not_ge,lt_iff_not_ge,Rat.num_nonneg]
  simp only [rational,numerator,denominator,RationalMetricInput.rationalBits,List.nil_append,
    List.cons_append,List.append_assoc,List.head?_cons,Option.getD_some,List.tail_cons,nat_code,
    extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.encode,Signed.encode,hs]
end MetricKMedianRecovery.BitMachine.BinaryInputParser

end OAI
