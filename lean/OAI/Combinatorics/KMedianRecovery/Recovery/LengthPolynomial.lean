import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack3

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake

noncomputable def PolyComputes.lengthPolynomial {f : List Bool → List Bool} (hf : PolyComputes f) : Polynomial ℕ :=
  Polynomial.X+hf.time*Polynomial.C hf.program.maxPush
lemma PolyComputes.length_bound {f : List Bool → List Bool} (hf : PolyComputes f) (x : List Bool) :
    (f x).length ≤ hf.lengthPolynomial.eval x.length := by
  simpa only [PolyComputes.lengthPolynomial,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_mul,Polynomial.eval_C] using hf.program.output_length (hf.outputs x)

namespace WordList

def cons (w ws : List Bool) : List Bool := true::pairBits (w,ws)
def encode : List (List Bool) → List Bool
  | []=>[]
  | w::ws=>cons w (encode ws)
def head (x : List Bool) : List Bool := extractPrefix x.tail
def tail (x : List Bool) : List Bool := discardPrefix x.tail
@[simp] lemma head_cons (w ws : List Bool) : head (cons w ws)=w := by
  simp only [head,cons,List.tail_cons,extractPrefix_pairBits]
@[simp] lemma tail_cons (w ws : List Bool) : tail (cons w ws)=ws := by
  simp only [tail,cons,List.tail_cons,discardPrefix_pairBits]
lemma cons_ne_nil (w ws : List Bool) : cons w ws≠[] := List.cons_ne_nil _ _
lemma length_cons (w ws : List Bool) : (cons w ws).length=2*w.length+ws.length+2 := by
  simp only [cons,List.length_cons,pairBits_length]; omega
lemma length_encode (ws : List (List Bool)) :
    (encode ws).length=2*(ws.map List.length).sum+2*ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [encode,length_cons,List.map_cons,List.sum_cons,List.length_cons,ih]; omega
lemma length_le_encode (ws : List (List Bool)) : ws.length ≤ (encode ws).length := by
  rw [length_encode]; omega
noncomputable def head_computes : PolyComputes head := tail_computes.comp extractPrefix_computes
noncomputable def tail_computes : PolyComputes tail :=
  WordOperations.tail_computes.comp discardPrefix_computes
noncomputable def cons_computes {h t : List Bool → List Bool} (hh : PolyComputes h) (ht : PolyComputes t) :
    PolyComputes (fun x=>cons (h x) (t x)) := (hh.pair ht).comp (prefix_computes true)
lemma head_length (x : List Bool) : (head x).length ≤ x.length := by
  have h := (ProductBits.projections_length x.tail).1
  simp only [List.length_tail] at h
  exact h.trans (Nat.sub_le _ _)
lemma tail_length (x : List Bool) : (tail x).length ≤ x.length-1 := by
  simpa only [tail,List.length_tail] using (ProductBits.projections_length x.tail).2

namespace ReverseMap

def step (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  if counter x=[] then pack false [] (data x) (output x)
  else pack true (WordList.tail (counter x)) (data x)
    (cons (f (pairBits (data x,head (counter x)))) (output x))
noncomputable def step_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (step f) := by
  have hn := (data_computes.pair (counter_computes.comp head_computes)).comp hf
  have ht := pack_computes true (counter_computes.comp tail_computes) data_computes
    (cons_computes hn output_computes)
  have hh := (counter_computes.comp isEmpty_computes).cond
    (pack_computes false (const_computes []) data_computes output_computes) ht
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq] using hh

def next (f : List Bool → List Bool) := While.next (step f)
lemma data_next (f : List Bool → List Bool) (x : List Bool) : data (next f x)=data x := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [data_pack]
  · rfl
lemma counter_next (f : List Bool → List Bool) (x : List Bool) :
    (counter (next f x)).length ≤ (counter x).length := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs
    · simp only [counter_pack,List.length_nil,Nat.zero_le]
    · simp only [counter_pack]; exact (tail_length _).trans (Nat.sub_le _ _)
  · exact le_rfl
lemma output_next {f : List Bool → List Bool} (hf : PolyComputes f) (x : List Bool) :
    (output (next f x)).length ≤ (output x).length+
      2*hf.lengthPolynomial.eval (2*(data x).length+1+(counter x).length)+2 := by
  have hp := hf.length_bound (pairBits (data x,head (counter x)))
  rw [pairBits_length] at hp
  have hl := head_length (counter x)
  have hm := polynomial_monotone hf.lengthPolynomial (show
    2*(data x).length+1+(head (counter x)).length ≤ 2*(data x).length+1+(counter x).length by omega)
  dsimp only at hm hp
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [output_pack,length_cons] <;> omega
  · omega
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
      have ht := tail_length (counter x)
      simp only [rank,head_pack,ite_true,counter_pack,hx]
      omega
  · simp only [rank,hx,ite_false,Nat.zero_sub,Nat.le_refl]

def growth (P : Polynomial ℕ) (x : List Bool) : ℕ := 2*P.eval (2*(data x).length+1+(counter x).length)+2
lemma iterate_bounds {f : List Bool → List Bool} (hf : PolyComputes f) (x : List Bool) (j : ℕ) :
    (counter ((next f)^[j] x)).length ≤ (counter x).length ∧ data ((next f)^[j] x)=data x ∧
    (output ((next f)^[j] x)).length ≤ (output x).length+j*growth hf.lengthPolynomial x ∧
    ((next f)^[j] x).length ≤ x.length+2*(counter x).length+2*(data x).length+(output x).length+
      j*growth hf.lengthPolynomial x+3 ∧ rank ((next f)^[j] x) ≤ rank x-j := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply,Nat.sub_zero,Nat.le_refl,Nat.zero_mul,
      Nat.add_zero,true_and,and_true]; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hc := counter_next f ((next f)^[j] x)
    have hd := data_next f ((next f)^[j] x)
    have ho := output_next hf ((next f)^[j] x)
    have hl := length_next f ((next f)^[j] x)
    have hr := rank_next f ((next f)^[j] x)
    rw [ih.2.1] at hd ho
    have hm := polynomial_monotone hf.lengthPolynomial
      (Nat.add_le_add_left ih.1 (2*(data x).length+1))
    dsimp only at hm
    have hog : (output (next f ((next f)^[j] x))).length ≤
        (output ((next f)^[j] x)).length+growth hf.lengthPolynomial x := by unfold growth; omega
    refine ⟨hc.trans ih.1,hd,?_,?_,?_⟩
    · nlinarith [ih.2.2.1]
    · apply hl.trans; apply max_le
      · nlinarith [ih.2.2.2.1]
      · rw [hd]; nlinarith [ih.1,ih.2.2.1]
    · omega
lemma stop {f : List Bool → List Bool} (hf : PolyComputes f) (x : List Bool) :
    ((next f)^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds hf x (rank x)).2.2.2.2
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro hp
  change (if ((next f)^[rank x] x).head?=some true then _ else 0)=0 at hh
  rw [ite_eq_left hp] at hh; omega
noncomputable def loop_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>(next f)^[rank x] x) := by
  let P := hf.lengthPolynomial
  apply (step_computes hf).whileLoop rank (Polynomial.X+1)
    ((Polynomial.X+1)*(2*(P.comp (3*Polynomial.X+1))+2)+6*Polynomial.X+3)
  · intro x
    have h := (projection_bounds x).1
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    unfold rank; split_ifs <;> omega
  · intro x j hj
    have h := (iterate_bounds hf x j).2.2.2.1
    obtain ⟨hc,hd,ho⟩ := projection_bounds x
    have hr : rank x ≤ x.length+1 := by unfold rank; split_ifs <;> omega
    have hm := polynomial_monotone P (show 2*(data x).length+1+(counter x).length ≤ 3*x.length+1 by omega)
    dsimp only at hm
    have hg : growth P x ≤ 2*P.eval (3*x.length+1)+2 := by unfold growth; omega
    have hjg := Nat.mul_le_mul (hj.trans hr) hg
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Polynomial.eval_one,Polynomial.eval_comp]
    change ((next f)^[j] x).length ≤ _
    change _ ≤ x.length+2*(counter x).length+2*(data x).length+(output x).length+j*growth P x+3 at h
    omega
  · exact stop hf

lemma next_nil (f : List Bool → List Bool) (d o : List Bool) :
    next f (pack true [] d o)=pack false [] d o := by
  simp only [next,While.next,head_pack,ite_true,step,counter_pack,data_pack,output_pack]
lemma next_cons (f : List Bool → List Bool) (w ws d o : List Bool) :
    next f (pack true (cons w ws) d o)=pack true ws d (cons (f (pairBits (d,w))) o) := by
  simp only [next,While.next,head_pack,ite_true,step,counter_pack,cons_ne_nil,ite_false,
    data_pack,output_pack,tail_cons,head_cons]
lemma loop_exact (f : List Bool → List Bool) (ws : List (List Bool)) (d : List Bool) (os : List (List Bool)) :
    (next f)^[ws.length+1] (pack true (encode ws) d (encode os))=
      pack false [] d (encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse++os)) := by
  induction ws generalizing os with
  | nil => simp only [encode,List.length_nil,Nat.zero_add,Function.iterate_one,next_nil,
      List.map_nil,List.reverse_nil,List.nil_append]
  | cons w ws ih =>
    rw [List.length_cons,Function.iterate_succ_apply,encode,next_cons]
    change (next f)^[ws.length+1] (pack true (encode ws) d (encode (f (pairBits (d,w))::os)))=_
    rw [ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
lemma loop_spec (f : List Bool → List Bool) (ws : List (List Bool)) (d : List Bool) :
    (next f)^[(encode ws).length+1] (pack true (encode ws) d [])=
      pack false [] d (encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse)) := by
  have hl := length_le_encode ws
  have hlen : (encode ws).length+1=((encode ws).length-ws.length)+(ws.length+1) := by omega
  rw [hlen,Function.iterate_add_apply]
  change (next f)^[_] ((next f)^[ws.length+1] (pack true (encode ws) d (encode [])))=_
  rw [loop_exact,List.append_nil]
  apply While.next_fixed
  exact (by decide : (some false:Option Bool)≠some true)

def run (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  let s := pack true (discardPrefix x) (extractPrefix x) []
  output ((next f)^[rank s] s)
noncomputable def run_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (run f) :=
  ((pack_computes true discardPrefix_computes extractPrefix_computes (const_computes [])).comp
    (loop_computes hf)).comp output_computes
lemma run_encode (f : List Bool → List Bool) (d : List Bool) (ws : List (List Bool)) :
    run f (pairBits (d,encode ws))=encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse) := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits,rank,head_pack,ite_true,counter_pack,
    loop_spec,output_pack]
end ReverseMap

def reverse (x : List Bool) : List Bool := ReverseMap.run discardPrefix (pairBits ([],x))
noncomputable def reverse_computes : PolyComputes reverse :=
  ((const_computes []).pair id_computes).comp (ReverseMap.run_computes discardPrefix_computes)
lemma reverse_encode (ws : List (List Bool)) : reverse (encode ws)=encode ws.reverse := by
  simp only [reverse,ReverseMap.run_encode,discardPrefix_pairBits,List.map_id']
def mapWith (f : List Bool → List Bool) : List Bool → List Bool := reverse ∘ ReverseMap.run f
noncomputable def mapWith_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (mapWith f) :=
  (ReverseMap.run_computes hf).comp reverse_computes
lemma mapWith_encode (f : List Bool → List Bool) (d : List Bool) (ws : List (List Bool)) :
    mapWith f (pairBits (d,encode ws))=encode (ws.map (fun w=>f (pairBits (d,w)))) := by
  simp only [mapWith,Function.comp_apply,ReverseMap.run_encode,reverse_encode,List.reverse_reverse]

end WordList
end MetricKMedianRecovery.BitMachine

end OAI
