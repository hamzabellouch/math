import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Copies
import OAI.Combinatorics.KMedianRecovery.Recovery.LengthPolynomial

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic
namespace WordList.Lookup

def step (x : List Bool) : List Bool :=
  if value (extractPrefix x)=0 then x
  else pairBits ((value (extractPrefix x)-1).bits,WordList.tail (discardPrefix x))
noncomputable def step_computes : PolyComputes step := by
  have hd := NatOps.sub extractPrefix_computes (const_computes [true])
  have hp := hd.pair (discardPrefix_computes.comp WordList.tail_computes)
  have hh := (NatOps.zero extractPrefix_computes).cond id_computes hp
  unfold step
  simpa [value,Function.comp_def] using hh
lemma decrement_length (x : List Bool) : (value x-1).bits.length ≤ x.length := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le_size (Nat.sub_le _ _) |>.trans
  simpa only [normalize_eq_bits,Nat.size_eq_bits_len] using BinaryDivision.normalize_length x
lemma first_step (x : List Bool) : (extractPrefix (step x)).length ≤ (extractPrefix x).length := by
  unfold step; split_ifs
  · exact le_rfl
  · rw [extractPrefix_pairBits]; exact decrement_length _
lemma rest_step (x : List Bool) : (discardPrefix (step x)).length ≤ (discardPrefix x).length := by
  unfold step; split_ifs
  · exact le_rfl
  · rw [discardPrefix_pairBits]; exact (WordList.tail_length _).trans (Nat.sub_le _ _)
lemma length_step (x : List Bool) : (step x).length ≤ max x.length
    (2*(extractPrefix x).length+1+(discardPrefix x).length) := by
  unfold step; split_ifs
  · exact Nat.le_max_left _ _
  · rw [pairBits_length]
    dsimp only
    have hi := decrement_length (extractPrefix x)
    have hl := WordList.tail_length (discardPrefix x)
    omega
lemma iterate_bounds (x : List Bool) (n : ℕ) :
    (extractPrefix (step^[n] x)).length ≤ (extractPrefix x).length ∧
    (discardPrefix (step^[n] x)).length ≤ (discardPrefix x).length ∧
    (step^[n] x).length ≤ max x.length (2*(extractPrefix x).length+1+(discardPrefix x).length) := by
  induction n with
  | zero => exact ⟨le_rfl,le_rfl,Nat.le_max_left _ _⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hf := first_step (step^[n] x)
    have hr := rest_step (step^[n] x)
    have hl := length_step (step^[n] x)
    exact ⟨hf.trans ih.1,hr.trans ih.2.1,by omega⟩

def run (x : List Bool) : List Bool := WordList.head (discardPrefix (step^[x.length] x))
noncomputable def run_computes : PolyComputes run := by
  have hi := BoundedIteration.polynomialRun_computes step_computes Polynomial.X (4*Polynomial.X+1)
  have hh := (hi.comp discardPrefix_computes).comp WordList.head_computes
  have he (x : List Bool) : BoundedIteration.polynomialRun step Polynomial.X (4*Polynomial.X+1) x=
      step^[x.length] x := by
    have ht := BoundedIteration.polynomialRun_eq step Polynomial.X (4*Polynomial.X+1) x (by
      intro j _
      have hb := (iterate_bounds x j).2.2
      obtain ⟨hf,hr⟩ := ProductBits.projections_length x
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
        Polynomial.eval_one]
      omega)
    simpa only [Polynomial.eval_X] using ht
  change PolyComputes (fun x=>WordList.head (discardPrefix (step^[x.length] x)))
  simpa only [Function.comp_def,he] using hh
lemma step_zero (ws : List (List Bool)) :
    step (pairBits (Nat.bits 0,encode ws))=pairBits (Nat.bits 0,encode ws) := by
  simp only [step,extractPrefix_pairBits,value_bits,ite_true]
lemma step_succ (i : ℕ) (ws : List (List Bool)) :
    step (pairBits ((i+1).bits,encode ws))=pairBits (i.bits,encode ws.tail) := by
  simp only [step,extractPrefix_pairBits,value_bits,Nat.add_eq_zero_iff,Nat.one_ne_zero,
    and_false,ite_false,Nat.add_sub_cancel,discardPrefix_pairBits]
  cases ws with
  | nil => rfl
  | cons w ws => simp only [encode,tail_cons,List.tail_cons]
lemma head_iterate (n i : ℕ) (ws : List (List Bool)) (hn : ws.length ≤ n) :
    WordList.head (discardPrefix (step^[n] (pairBits (i.bits,encode ws))))=ws[i]?.getD [] := by
  induction n generalizing i ws with
  | zero =>
    have hw : ws=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst ws
    simp only [Function.iterate_zero_apply,discardPrefix_pairBits,encode,List.getElem?_nil,Option.getD_none]
    rfl
  | succ n ih =>
    cases i with
    | zero =>
      rw [Function.iterate_fixed (step_zero ws)]
      rw [discardPrefix_pairBits]
      cases ws with
      | nil => rfl
      | cons w ws => simp only [encode,head_cons,List.getElem?_cons_zero,Option.getD_some]
    | succ i =>
      rw [Function.iterate_succ_apply,step_succ]
      have hl : ws.tail.length ≤ n := by simp only [List.length_tail]; omega
      rw [ih i ws.tail hl]
      cases ws <;> rfl
lemma run_encode (i : ℕ) (ws : List (List Bool)) :
    run (pairBits (i.bits,encode ws))=ws[i]?.getD [] := by
  apply head_iterate
  have h := length_le_encode ws
  rw [pairBits_length]
  dsimp only
  omega
end WordList.Lookup
end
open WordOperations
namespace WordList
lemma length_encode_append (xs ys : List (List Bool)) :
    (encode (xs++ys)).length=(encode xs).length+(encode ys).length := by
  induction xs with
  | nil => simp only [List.nil_append,encode,List.length_nil,Nat.zero_add]
  | cons x xs ih => simp only [List.cons_append,encode,length_cons,ih]; omega
lemma length_encode_drop (xs : List (List Bool)) (n : ℕ) :
    (encode (xs.drop n)).length ≤ (encode xs).length := by
  have h := length_encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  omega
namespace Fold

def pack (ws ctx a : List Bool) : List Bool := pairBits (ws,pairBits (ctx,a))
def items (x : List Bool) := extractPrefix x
def context (x : List Bool) := extractPrefix (discardPrefix x)
def accum (x : List Bool) := discardPrefix (discardPrefix x)
@[simp] lemma items_pack (ws ctx a : List Bool) : items (pack ws ctx a)=ws := by
  simp only [items,pack,extractPrefix_pairBits]
@[simp] lemma context_pack (ws ctx a : List Bool) : context (pack ws ctx a)=ctx := by
  simp only [context,pack,extractPrefix_pairBits,discardPrefix_pairBits]
@[simp] lemma accum_pack (ws ctx a : List Bool) : accum (pack ws ctx a)=a := by
  simp only [accum,pack,discardPrefix_pairBits]
lemma length_pack (ws ctx a : List Bool) : (pack ws ctx a).length=2*ws.length+2*ctx.length+a.length+2 := by
  simp only [pack,pairBits_length]; omega
noncomputable def items_computes : PolyComputes items := extractPrefix_computes
noncomputable def context_computes : PolyComputes context := discardPrefix_computes.comp extractPrefix_computes
noncomputable def accum_computes : PolyComputes accum := discardPrefix_computes.comp discardPrefix_computes
noncomputable def pack_computes {w c a : List Bool → List Bool} (hw : PolyComputes w)
    (hc : PolyComputes c) (ha : PolyComputes a) : PolyComputes (fun x=>pack (w x) (c x) (a x)) :=
  hw.pair (hc.pair ha)

def step (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  if items x=[] then x else pack (WordList.tail (items x)) (context x)
    (f (pairBits (context x,pairBits (WordList.head (items x),accum x))))
noncomputable def step_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (step f) := by
  have ha := (context_computes.pair ((items_computes.comp head_computes).pair accum_computes)).comp hf
  have ht := pack_computes (items_computes.comp tail_computes) context_computes ha
  have hh := (items_computes.comp isEmpty_computes).cond id_computes ht
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq,id_eq] using hh

def operation (f : List Bool → List Bool) (ctx : List Bool) (a w : List Bool) : List Bool :=
  f (pairBits (ctx,pairBits (w,a)))
lemma step_nil (f : List Bool → List Bool) (ctx a : List Bool) :
    step f (pack (encode []) ctx a)=pack (encode []) ctx a := by
  simp only [step,items_pack,encode,ite_true]
lemma step_cons (f : List Bool → List Bool) (ctx a w : List Bool) (ws : List (List Bool)) :
    step f (pack (encode (w::ws)) ctx a)=pack (encode ws) ctx (operation f ctx a w) := by
  simp only [step,items_pack,encode,cons_ne_nil,ite_false,context_pack,head_cons,tail_cons,accum_pack,operation]
lemma iterate_pack (f : List Bool → List Bool) (ctx a : List Bool) (ws : List (List Bool)) (n : ℕ) :
    (step f)^[n] (pack (encode ws) ctx a)=
      pack (encode (ws.drop n)) ctx ((ws.take n).foldl (operation f ctx) a) := by
  induction n generalizing ws a with
  | zero => simp only [Function.iterate_zero_apply,List.drop_zero,List.take_zero,List.foldl_nil]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases ws with
    | nil =>
      rw [step_nil,Function.iterate_fixed (step_nil f ctx a)]
      rfl
    | cons w ws =>
      rw [step_cons,ih]
      simp only [List.drop_succ_cons,List.take_succ_cons,List.foldl_cons]

noncomputable def run (f : List Bool → List Bool) (R : Polynomial ℕ) : List Bool → List Bool :=
  accum ∘ BoundedIteration.polynomialRun (step f) Polynomial.X R
noncomputable def run_computes {f : List Bool → List Bool} (hf : PolyComputes f) (R : Polynomial ℕ) :
    PolyComputes (run f R) :=
  (BoundedIteration.polynomialRun_computes (step_computes hf) Polynomial.X R).comp accum_computes

lemma run_encode (f : List Bool → List Bool) (R : Polynomial ℕ) (ctx a : List Bool)
    (ws : List (List Bool)) (B : ℕ)
    (hB : ∀ n,((ws.take n).foldl (operation f ctx) a).length ≤ B)
    (hR : 2*(encode ws).length+2*ctx.length+B+2 ≤ R.eval (pack (encode ws) ctx a).length) :
    run f R (pack (encode ws) ctx a)=ws.foldl (operation f ctx) a := by
  have he := BoundedIteration.polynomialRun_eq (step f) Polynomial.X R (pack (encode ws) ctx a) (by
    intro j _
    rw [iterate_pack,length_pack]
    have hd := length_encode_drop ws j
    have hb := hB j
    omega)
  simp only [run,Function.comp_apply,he,Polynomial.eval_X,iterate_pack,accum_pack]
  rw [List.take_of_length_le]
  have hw := length_le_encode ws
  rw [length_pack]
  omega
end Fold
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
