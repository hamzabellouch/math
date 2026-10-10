import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack3

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake
namespace BoundedIteration

def step (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  if counter x=[] then pack false [] (data x) (output x)
  else pack true (counter x).tail (data x) ((f (output x)).take (data x).length)
noncomputable def step_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (step f) := by
  have hu := (data_computes.pair (output_computes.comp hf)).comp takeWords_computes
  have ht := pack_computes true (counter_computes.comp tail_computes) data_computes hu
  have hh := (counter_computes.comp isEmpty_computes).cond
    (pack_computes false (const_computes []) data_computes output_computes) ht
  unfold step
  simpa only [Function.comp_def,takeWords,extractPrefix_pairBits,discardPrefix_pairBits,
    decide_eq_true_eq] using hh

def next (f : List Bool → List Bool) := While.next (step f)
lemma data_next (f : List Bool → List Bool) (x : List Bool) : data (next f x)=data x := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [data_pack]
  · rfl
lemma counter_next (f : List Bool → List Bool) (x : List Bool) :
    (counter (next f x)).length ≤ (counter x).length := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [counter_pack,List.length_nil,List.length_tail] <;> omega
  · exact le_rfl
lemma output_next (f : List Bool → List Bool) (x : List Bool) :
    (output (next f x)).length ≤ max (output x).length (data x).length := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs
    · simp only [output_pack]; exact Nat.le_max_left _ _
    · simp only [output_pack,List.length_take]; omega
  · exact Nat.le_max_left _ _
lemma length_next (f : List Bool → List Bool) (x : List Bool) :
    (next f x).length ≤ max x.length
      (2*(counter (next f x)).length+2*(data (next f x)).length+(output (next f x)).length+3) := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [length_pack,counter_pack,data_pack,output_pack] <;> omega
  · exact Nat.le_max_left _ _
lemma rank_next (f : List Bool → List Bool) (x : List Bool) : rank (next f x) ≤ rank x-1 := by
  unfold next While.next; split_ifs with hx
  · unfold step
    by_cases hc : counter x=[]
    · rw [ite_eq_left hc]
      simp only [rank,head_pack,Option.some.injEq,Bool.false_eq_true,ite_false,Nat.zero_le]
    · rw [ite_eq_right hc]
      have hp := List.length_pos_iff.mpr hc
      simp only [rank,head_pack,ite_true,counter_pack,List.length_tail,hx]
      omega
  · simp only [rank,hx,ite_false,Nat.zero_sub,Nat.le_refl]

lemma iterate_bounds (f : List Bool → List Bool) (x : List Bool) (j : ℕ) :
    (counter ((next f)^[j] x)).length ≤ (counter x).length ∧
    data ((next f)^[j] x)=data x ∧
    (output ((next f)^[j] x)).length ≤ max (output x).length (data x).length ∧
    ((next f)^[j] x).length ≤ x.length+2*(counter x).length+3*(data x).length+(output x).length+3 ∧
    rank ((next f)^[j] x) ≤ rank x-j := by
  induction j with
  | zero =>
    simp only [Function.iterate_zero_apply,Nat.sub_zero,Nat.le_refl,true_and,and_true]
    exact ⟨Nat.le_max_left _ _,by omega⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hc := counter_next f ((next f)^[j] x)
    have hd := data_next f ((next f)^[j] x)
    have ho := output_next f ((next f)^[j] x)
    have hl := length_next f ((next f)^[j] x)
    have hr := rank_next f ((next f)^[j] x)
    rw [ih.2.1] at hd ho
    refine ⟨hc.trans ih.1,hd,?_,?_,?_⟩
    · omega
    · apply hl.trans; apply max_le ih.2.2.2.1
      rw [hd]
      omega
    · omega
lemma stop (f : List Bool → List Bool) (x : List Bool) : ((next f)^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds f x (rank x)).2.2.2.2
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro hp
  change (if ((next f)^[rank x] x).head?=some true then _ else 0)=0 at hh
  rw [ite_eq_left hp] at hh; omega
noncomputable def loop_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>(next f)^[rank x] x) := by
  apply (step_computes hf).whileLoop rank (Polynomial.X+1) (7*Polynomial.X+3)
  · intro x
    have h := (projection_bounds x).1
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    unfold rank; split_ifs <;> omega
  · intro x j _
    have h := (iterate_bounds f x j).2.2.2.1
    obtain ⟨hc,hd,ho⟩ := projection_bounds x
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    change ((next f)^[j] x).length ≤ _
    omega
  · exact stop f

lemma next_nil (f : List Bool → List Bool) (d o : List Bool) :
    next f (pack true [] d o)=pack false [] d o := by
  simp only [next,While.next,head_pack,ite_true,step,counter_pack,data_pack,output_pack]
lemma next_cons (f : List Bool → List Bool) (b : Bool) (c d o : List Bool) :
    next f (pack true (b::c) d o)=pack true c d ((f o).take d.length) := by
  simp only [next,While.next,head_pack,ite_true,step,counter_pack,reduceCtorEq,ite_false,
    data_pack,output_pack,List.tail_cons]
lemma loop_spec (f : List Bool → List Bool) (c d o : List Bool) :
    (next f)^[c.length+1] (pack true c d o)=
    pack false [] d ((fun s=>(f s).take d.length)^[c.length] o) := by
  induction c generalizing o with
  | nil => simp only [List.length_nil,Nat.zero_add,Function.iterate_one,next_nil,
      Function.iterate_zero_apply]
  | cons b c ih =>
    rw [List.length_cons,Function.iterate_succ_apply,next_cons,ih,Function.iterate_succ_apply]

def run (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  (fun s=>(f s).take (extractPrefix (discardPrefix x)).length)^[(extractPrefix x).length]
    (discardPrefix (discardPrefix x))
noncomputable def run_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (run f) := by
  have hi := pack_computes true extractPrefix_computes
    (discardPrefix_computes.comp extractPrefix_computes)
    (discardPrefix_computes.comp discardPrefix_computes)
  have hh := (hi.comp (loop_computes hf)).comp output_computes
  convert hh using 1
  funext x
  simp only [Function.comp_apply,rank,head_pack,ite_true,counter_pack,loop_spec,output_pack]
  rfl
lemma run_pair (f : List Bool → List Bool) (c d s : List Bool) :
    run f (pairBits (c,pairBits (d,s)))=(fun s=>(f s).take d.length)^[c.length] s := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits]
lemma clamp_iterate_eq (f : List Bool → List Bool) (d n : ℕ) (s : List Bool)
    (h : ∀ j, j ≤ n → (f^[j] s).length ≤ d) :
    (fun s=>(f s).take d)^[n] s=f^[n] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih (fun j hj=>h j (by omega))]
    simpa only [Function.iterate_succ_apply'] using List.take_of_length_le (by simpa only [Function.iterate_succ_apply'] using h (n+1) le_rfl)
lemma run_eq (f : List Bool → List Bool) (c d s : List Bool)
    (h : ∀ j, j ≤ c.length → (f^[j] s).length ≤ d.length) :
    run f (pairBits (c,pairBits (d,s)))=f^[c.length] s := by
  rw [run_pair]; exact clamp_iterate_eq f d.length c.length s h

end BoundedIteration
end MetricKMedianRecovery.BitMachine

end OAI
