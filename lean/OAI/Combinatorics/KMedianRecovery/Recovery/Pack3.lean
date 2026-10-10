import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LeftNum

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryTake

def pack (a : Bool) (c d o : List Bool) : List Bool := a::pairBits (c,pairBits (d,o))
@[simp] lemma head_pack (a : Bool) (c d o : List Bool) : (pack a c d o).head?=some a := rfl
def counter (x : List Bool) := extractPrefix x.tail
def data (x : List Bool) := extractPrefix (discardPrefix x.tail)
def output (x : List Bool) := discardPrefix (discardPrefix x.tail)
@[simp] lemma counter_pack (a : Bool) (c d o : List Bool) : counter (pack a c d o)=c := by
  simp only [counter,pack,List.tail_cons,extractPrefix_pairBits]
@[simp] lemma data_pack (a : Bool) (c d o : List Bool) : data (pack a c d o)=d := by
  simp only [data,pack,List.tail_cons,extractPrefix_pairBits,discardPrefix_pairBits]
@[simp] lemma output_pack (a : Bool) (c d o : List Bool) : output (pack a c d o)=o := by
  simp only [output,pack,List.tail_cons,discardPrefix_pairBits]
lemma length_pack (a : Bool) (c d o : List Bool) :
    (pack a c d o).length=2*c.length+2*d.length+o.length+3 := by
  simp only [pack,List.length_cons,pairBits_length]; omega
noncomputable def counter_computes : PolyComputes counter := tail_computes.comp extractPrefix_computes
noncomputable def data_computes : PolyComputes data :=
  (tail_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def output_computes : PolyComputes output :=
  (tail_computes.comp discardPrefix_computes).comp discardPrefix_computes
noncomputable def pack_computes {c d o : List Bool → List Bool} (a : Bool)
    (hc : PolyComputes c) (hd : PolyComputes d) (ho : PolyComputes o) :
    PolyComputes (fun x=>pack a (c x) (d x) (o x)) :=
  (const_computes [a]).append (hc.pair (hd.pair ho))

def step (x : List Bool) : List Bool :=
  if counter x=[] then pack false [] (data x) (output x)
  else pack true (counter x).tail (data x).tail
    (if data x=[] then output x else (data x).head?.getD false::output x)
noncomputable def step_computes : PolyComputes step := by
  have hc := counter_computes.comp isEmpty_computes
  have hd := data_computes.comp isEmpty_computes
  have ho := hd.cond output_computes ((data_computes.comp head_computes).append output_computes)
  have ht := pack_computes true (counter_computes.comp tail_computes)
    (data_computes.comp tail_computes) ho
  have hh := hc.cond (pack_computes false (const_computes []) data_computes output_computes) ht
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq,List.singleton_append] using hh

def next := While.next step
def mass (x : List Bool) : ℕ := (counter x).length+(data x).length+(output x).length
def rank (x : List Bool) : ℕ := if x.head?=some true then (counter x).length+1 else 0
lemma projection_bounds (x : List Bool) :
    (counter x).length ≤ x.length ∧ (data x).length ≤ x.length ∧ (output x).length ≤ x.length := by
  have h0 : x.tail.length ≤ x.length := by simp only [List.length_tail]; omega
  have h1 := ProductBits.projections_length x.tail
  have h2 := ProductBits.projections_length (discardPrefix x.tail)
  dsimp only [counter,data,output]; omega
lemma mass_next (x : List Bool) : mass (next x) ≤ mass x := by
  unfold next While.next
  split_ifs
  · unfold step
    by_cases hc : counter x=[]
    · rw [ite_eq_left hc]
      simp only [mass,counter_pack,data_pack,output_pack,List.length_nil]
      omega
    · rw [ite_eq_right hc]
      have hp := List.length_pos_iff.mpr hc
      split_ifs <;> simp only [mass,counter_pack,data_pack,output_pack,List.length_tail,List.length_cons] <;> omega
  · exact le_rfl
lemma length_next (x : List Bool) : (next x).length ≤ max x.length (2*mass (next x)+3) := by
  unfold next While.next
  split_ifs
  · unfold step
    split_ifs <;> simp only [length_pack,mass,counter_pack,data_pack,output_pack,
      List.length_nil,List.length_tail,List.length_cons] <;> omega
  · exact Nat.le_max_left _ _
lemma rank_next (x : List Bool) : rank (next x) ≤ rank x-1 := by
  unfold next While.next
  split_ifs with hx
  · unfold step
    by_cases hc : counter x=[]
    · rw [ite_eq_left hc]
      simp only [rank,head_pack,Option.some.injEq,Bool.false_eq_true,ite_false,Nat.zero_le]
    · rw [ite_eq_right hc]
      have hp : 0<(counter x).length := List.length_pos_iff.mpr hc
      simp only [rank,head_pack,ite_true,counter_pack,List.length_tail,hx]
      omega
  · simp only [rank,hx,ite_false,Nat.zero_sub,Nat.le_refl]
lemma iterate_bounds (x : List Bool) (j : ℕ) :
    mass (next^[j] x) ≤ mass x ∧ (next^[j] x).length ≤ x.length+2*mass x+3 ∧
    rank (next^[j] x) ≤ rank x-j := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply,Nat.sub_zero,Nat.le_refl,true_and,and_true]; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hm := mass_next (next^[j] x)
    have hl := length_next (next^[j] x)
    have hr := rank_next (next^[j] x)
    refine ⟨hm.trans ih.1,?_,?_⟩
    · apply hl.trans; apply max_le ih.2.1; omega
    · omega
lemma stop (x : List Bool) : (next^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds x (rank x)).2.2
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro hp
  change (if (next^[rank x] x).head?=some true then _ else 0)=0 at hh
  rw [ite_eq_left hp] at hh
  omega
noncomputable def loop_computes : PolyComputes (fun x=>next^[rank x] x) := by
  apply step_computes.whileLoop rank (Polynomial.X+1) (7*Polynomial.X+3)
  · intro x
    have h := (projection_bounds x).1
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    unfold rank; split_ifs <;> omega
  · intro x j _
    have h := (iterate_bounds x j).2.1
    obtain ⟨hc,hd,ho⟩ := projection_bounds x
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    change (next^[j] x).length ≤ _
    unfold mass at h
    omega
  · exact stop

lemma next_nil (d o : List Bool) : next (pack true [] d o)=pack false [] d o := by
  simp only [next,While.next,pack,List.head?_cons,ite_true,step,counter,List.tail_cons,
    extractPrefix_pairBits,data,discardPrefix_pairBits,output]
lemma next_cons (b : Bool) (c d o : List Bool) : next (pack true (b::c) d o)=
    pack true c d.tail (if d=[] then o else d.head?.getD false::o) := by
  simp only [next,While.next,pack,List.head?_cons,ite_true,step,counter,List.tail_cons,
    extractPrefix_pairBits,reduceCtorEq,ite_false,data,discardPrefix_pairBits,output]
lemma loop_spec (c d o : List Bool) : next^[c.length+1] (pack true c d o)=
    pack false [] (d.drop c.length) ((d.take c.length).reverse++o) := by
  induction c generalizing d o with
  | nil => simp only [List.length_nil,Nat.zero_add,Function.iterate_one,next_nil,
      List.drop_zero,List.take_zero,List.reverse_nil,List.nil_append]
  | cons b c ih =>
    rw [List.length_cons,show c.length+1+1=(c.length+1)+1 from rfl,
      Function.iterate_succ_apply,next_cons,ih]
    cases d with
    | nil => simp only [List.tail_nil,ite_true,List.drop_nil,List.take_nil,List.reverse_nil,List.nil_append]
    | cons a d => simp only [List.tail_cons,reduceCtorEq,ite_false,List.head?_cons,Option.getD_some,
        List.drop_succ_cons,List.take_succ_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

def takeWords (x : List Bool) : List Bool := (discardPrefix x).take (extractPrefix x).length
noncomputable def takeWords_computes : PolyComputes takeWords := by
  have hi := pack_computes true extractPrefix_computes discardPrefix_computes (const_computes [])
  have hh := ((hi.comp loop_computes).comp output_computes).comp reverse_computes
  convert hh using 1
  funext x
  simp only [Function.comp_apply,rank,pack,List.head?_cons,ite_true,counter,List.tail_cons,
    extractPrefix_pairBits]
  change takeWords x=(output (next^[(extractPrefix x).length+1]
    (pack true (extractPrefix x) (discardPrefix x) []))).reverse
  rw [loop_spec,output_pack,List.append_nil,List.reverse_reverse]
  rfl

end UnaryTake
end MetricKMedianRecovery.BitMachine

end OAI
