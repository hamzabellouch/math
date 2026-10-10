import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Step

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake
namespace RepeatedAppend

def copies : ℕ → List Bool → List Bool
  | 0,_=>[]
  | n+1,d=>copies n d++d
lemma length_copies (n : ℕ) (d : List Bool) : (copies n d).length=n*d.length := by
  induction n with
  | zero => simp only [copies,List.length_nil,Nat.zero_mul]
  | succ n ih => simp only [copies,List.length_append,ih,Nat.add_mul,Nat.one_mul]

def step (x : List Bool) : List Bool :=
  if counter x=[] then pack false [] (data x) (output x)
  else pack true (counter x).tail (data x) (data x++output x)
noncomputable def step_computes : PolyComputes step := by
  have ht := pack_computes true (counter_computes.comp tail_computes) data_computes
    (data_computes.append output_computes)
  have hh := (counter_computes.comp isEmpty_computes).cond
    (pack_computes false (const_computes []) data_computes output_computes) ht
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq] using hh

def next := While.next step
lemma data_next (x : List Bool) : data (next x)=data x := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [data_pack]
  · rfl
lemma counter_next (x : List Bool) : (counter (next x)).length ≤ (counter x).length := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [counter_pack,List.length_nil,List.length_tail] <;> omega
  · exact le_rfl
lemma output_next (x : List Bool) : (output (next x)).length ≤ (output x).length+(data x).length := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [output_pack,List.length_append] <;> omega
  · omega
lemma length_next (x : List Bool) :
    (next x).length ≤ max x.length
      (2*(counter (next x)).length+2*(data (next x)).length+(output (next x)).length+3) := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [length_pack,counter_pack,data_pack,output_pack] <;> omega
  · exact Nat.le_max_left _ _
lemma rank_next (x : List Bool) : rank (next x) ≤ rank x-1 := by
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
lemma iterate_bounds (x : List Bool) (j : ℕ) :
    (counter (next^[j] x)).length ≤ (counter x).length ∧ data (next^[j] x)=data x ∧
    (output (next^[j] x)).length ≤ (output x).length+j*(data x).length ∧
    (next^[j] x).length ≤ x.length+2*(counter x).length+2*(data x).length+(output x).length+
      j*(data x).length+3 ∧ rank (next^[j] x) ≤ rank x-j := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply,Nat.sub_zero,Nat.le_refl,Nat.zero_mul,
      Nat.add_zero,true_and,and_true]; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hc := counter_next (next^[j] x)
    have hd := data_next (next^[j] x)
    have ho := output_next (next^[j] x)
    have hl := length_next (next^[j] x)
    have hr := rank_next (next^[j] x)
    rw [ih.2.1] at hd ho
    refine ⟨hc.trans ih.1,hd,?_,?_,?_⟩
    · nlinarith [ih.2.2.1]
    · apply hl.trans; apply max_le
      · nlinarith [ih.2.2.2.1]
      · rw [hd]; nlinarith [ih.1,ih.2.2.1]
    · omega
lemma stop (x : List Bool) : (next^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds x (rank x)).2.2.2.2
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro hp
  change (if (next^[rank x] x).head?=some true then _ else 0)=0 at hh
  rw [ite_eq_left hp] at hh; omega
noncomputable def loop_computes : PolyComputes (fun x=>next^[rank x] x) := by
  apply step_computes.whileLoop rank (Polynomial.X+1) (20*(Polynomial.X+1)^2)
  · intro x
    have h := (projection_bounds x).1
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    unfold rank; split_ifs <;> omega
  · intro x j hj
    have h := (iterate_bounds x j).2.2.2.1
    obtain ⟨hc,hd,ho⟩ := projection_bounds x
    have hr : rank x ≤ x.length+1 := by unfold rank; split_ifs <;> omega
    have hjd : j*(data x).length ≤ (x.length+1)*x.length := Nat.mul_le_mul (hj.trans hr) hd
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    change (next^[j] x).length ≤ _
    nlinarith
  · exact stop
lemma next_nil (d o : List Bool) : next (pack true [] d o)=pack false [] d o := by
  simp only [next,While.next,head_pack,ite_true,step,counter_pack,data_pack,output_pack]
lemma next_cons (b : Bool) (c d o : List Bool) :
    next (pack true (b::c) d o)=pack true c d (d++o) := by
  simp only [next,While.next,head_pack,ite_true,step,counter_pack,reduceCtorEq,ite_false,
    data_pack,output_pack,List.tail_cons]
lemma loop_spec (c d o : List Bool) : next^[c.length+1] (pack true c d o)=
    pack false [] d (copies c.length d++o) := by
  induction c generalizing o with
  | nil => simp only [List.length_nil,Nat.zero_add,Function.iterate_one,next_nil,copies,List.nil_append]
  | cons b c ih => rw [List.length_cons,Function.iterate_succ_apply,next_cons,ih,copies,List.append_assoc]

def run (x : List Bool) : List Bool := copies (extractPrefix x).length (discardPrefix x)
noncomputable def run_computes : PolyComputes run := by
  have hi := pack_computes true extractPrefix_computes discardPrefix_computes (const_computes [])
  have hh := (hi.comp loop_computes).comp output_computes
  convert hh using 1
  funext x
  simp only [Function.comp_apply,rank,head_pack,ite_true,counter_pack,loop_spec,output_pack,List.append_nil]
  rfl
lemma run_pair (c d : List Bool) : run (pairBits (c,d))=copies c.length d := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits]

end RepeatedAppend

structure PolynomialCounter (P : Polynomial ℕ) where
  word : List Bool → List Bool
  computes : PolyComputes word
  word_length : ∀ x,(word x).length=P.eval x.length
namespace PolynomialCounter
noncomputable def constant (n : ℕ) : PolynomialCounter (Polynomial.C n) where
  word _ := List.replicate n false
  computes := const_computes (List.replicate n false)
  word_length x := by simp only [List.length_replicate,Polynomial.eval_C]
noncomputable def identity : PolynomialCounter Polynomial.X where
  word := id
  computes := id_computes
  word_length x := by simp only [id_eq,Polynomial.eval_X]
noncomputable def add {P Q : Polynomial ℕ} (p : PolynomialCounter P) (q : PolynomialCounter Q) :
    PolynomialCounter (P+Q) where
  word x := p.word x++q.word x
  computes := p.computes.append q.computes
  word_length x := by simp only [List.length_append,p.word_length,q.word_length,Polynomial.eval_add]
noncomputable def mul {P Q : Polynomial ℕ} (p : PolynomialCounter P) (q : PolynomialCounter Q) :
    PolynomialCounter (P*Q) where
  word x := RepeatedAppend.copies (p.word x).length (q.word x)
  computes := by
    have hh := (p.computes.pair q.computes).comp RepeatedAppend.run_computes
    simpa only [Function.comp_def,RepeatedAppend.run_pair] using hh
  word_length x := by simp only [RepeatedAppend.length_copies,p.word_length,q.word_length,Polynomial.eval_mul]

theorem nonempty (P : Polynomial ℕ) : Nonempty (PolynomialCounter P) := by
  induction P using Polynomial.induction_on with
  | C n => exact ⟨constant n⟩
  | add P Q hp hq => obtain ⟨p⟩ := hp; obtain ⟨q⟩ := hq; exact ⟨p.add q⟩
  | monomial n a ih =>
    obtain ⟨p⟩ := ih
    rw [pow_succ,←mul_assoc]
    exact ⟨p.mul identity⟩
noncomputable def choose (P : Polynomial ℕ) : PolynomialCounter P := Classical.choice (nonempty P)
end PolynomialCounter

namespace BoundedIteration

def polynomialRun (f : List Bool → List Bool) (Q R : Polynomial ℕ) (x : List Bool) : List Bool :=
  (fun s=>(f s).take (R.eval x.length))^[Q.eval x.length] x
noncomputable def polynomialRun_computes {f : List Bool → List Bool} (hf : PolyComputes f)
    (Q R : Polynomial ℕ) : PolyComputes (polynomialRun f Q R) := by
  let q := PolynomialCounter.choose Q
  let r := PolynomialCounter.choose R
  have hh := (q.computes.pair (r.computes.pair id_computes)).comp (run_computes hf)
  unfold polynomialRun
  simpa only [Function.comp_def,run_pair,q.word_length,r.word_length,id_eq] using hh
lemma polynomialRun_eq (f : List Bool → List Bool) (Q R : Polynomial ℕ) (x : List Bool)
    (h : ∀ j, j ≤ Q.eval x.length → (f^[j] x).length ≤ R.eval x.length) :
    polynomialRun f Q R x=f^[Q.eval x.length] x :=
  clamp_iterate_eq f (R.eval x.length) (Q.eval x.length) x h
end BoundedIteration
end MetricKMedianRecovery.BitMachine

end OAI
