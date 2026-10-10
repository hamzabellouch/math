import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack2
import OAI.Combinatorics.KMedianRecovery.Recovery.Mul

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open Turing Turing.TM2 StateTransition
namespace BinaryArithmetic.Multiplication

noncomputable def process_outputs (xs ys acc : List Bool) (B : ℕ)
    (hB : acc.length+xs.length*(ys.length+2)≤B) :
    EvalsToInTime program.machine.step (cfg 1 false ys xs [] acc [])
      (some (done (mulFrom xs ys acc))) (10*(xs.length+1)*(B+ys.length+2)) := by
  induction xs generalizing acc with
  | nil =>
    have hh := step_then (process_nil ys acc) (clear_outputs ys acc)
    exact time_mono hh (by simp only [List.length_nil]; omega)
  | cons b xs ih =>
    have hacc : acc.length≤B := by omega
    cases b with
    | false =>
      have hB' : (false::acc).length+xs.length*(ys.length+2)≤B := by
        simp only [List.length_cons,Nat.add_mul] at hB ⊢
        omega
      have hh := step_then (process_false xs ys acc) (ih (false::acc) hB')
      change EvalsToInTime program.machine.step _ (some (done (mulFrom xs ys (false::acc)))) _
      exact time_mono hh (by simp only [List.length_cons]; nlinarith)
    | true =>
      have hl := add_length false ys (false::acc)
      have hB' : (add false ys (false::acc)).length+xs.length*(ys.length+2)≤B := by
        simp only [List.length_cons,Nat.add_mul] at hB hl ⊢
        omega
      have hh := eval_trans (add_cycle xs ys (false::acc)) (ih _ hB')
      have hh' := step_then (process_true xs ys acc) hh
      change EvalsToInTime program.machine.step _
        (some (done (mulFrom xs ys (add false ys (false::acc))))) _
      exact time_mono hh' (by simp only [List.length_cons] at hl ⊢; nlinarith)

noncomputable def parse_phase (xs bs : List Bool) :
    EvalsToInTime program.machine.step (cfg 0 false xs bs [] [] [])
      (some (cfg 1 false (discardPrefix xs) ((extractPrefix xs).reverse++bs) [] [] [])) (xs.length+1) := by
  induction xs using List.twoStepInduction generalizing bs with
  | nil => exact one_step (parse_nil bs)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_false [] bs)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_one bs)) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false (c::xs) bs)) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (parse_true c xs bs) (ih (c::bs))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

lemma projections_length (xs : List Bool) :
    (extractPrefix xs).length≤xs.length ∧ (discardPrefix xs).length≤xs.length := by
  induction xs using List.twoStepInduction with
  | nil => simp [extractPrefix,discardPrefix]
  | singleton b => cases b <;> simp [extractPrefix,discardPrefix]
  | cons_cons b c xs ih _ => cases b <;> simp only [extractPrefix,discardPrefix,List.length_cons,List.length_nil] <;> omega

noncomputable def raw_computes : PolyComputes (fun xs =>
    mulFrom (extractPrefix xs).reverse (discardPrefix xs) []) where
  program := program
  time := 30*(Polynomial.X+1)^3
  outputs xs := by
    let n := xs.length
    let x := (extractPrefix xs).reverse
    let y := discardPrefix xs
    have hx : x.length≤n := by simpa only [x,List.length_reverse] using (projections_length xs).1
    have hy : y.length≤n := (projections_length xs).2
    have h1 := parse_phase xs []
    simp only [List.append_nil] at h1
    have h2 := process_outputs x y [] (n*(n+2)) (by
      simp only [List.length_nil,Nat.zero_add]
      exact Nat.mul_le_mul hx (Nat.add_le_add_right hy 2))
    have hh := eval_trans h1 h2
    change TM2OutputsInTime program.machine xs
      (some (mulFrom x y [])) _
    simp only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    apply time_mono hh
    have htime : 10*(x.length+1)*(n*(n+2)+y.length+2)≤
        10*(n+1)*(n*(n+2)+n+2) := by gcongr
    change 10*(x.length+1)*(n*(n+2)+y.length+2)+(n+1)≤30*(n+1)^3
    calc
      _ ≤ 10*(n+1)*(n*(n+2)+n+2)+(n+1) := Nat.add_le_add_right htime _
      _ ≤ _ := by nlinarith [Nat.zero_le (n^3)]

end BinaryArithmetic.Multiplication
namespace BinaryArithmetic

noncomputable def normalize_computes : PolyComputes normalize :=
  (reverse_computes.comp trim_computes).comp reverse_computes

noncomputable def multiply_computes : PolyComputes (fun xs =>
    normalize (mulFrom (extractPrefix xs).reverse (discardPrefix xs) [])) :=
  Multiplication.raw_computes.comp normalize_computes

noncomputable def multiplication : Turing.TM2ComputableInPolyTime
    (fun p : ℕ×ℕ => pairBits (p.1.bits,p.2.bits)) Nat.bits (fun p => p.1*p.2) :=
  multiply_computes.reencode _ _ (fun p => by
    simp only [pairBits,extractPrefix_pair,discardPrefix_pair,normalize_mulFrom,value_bits])

end BinaryArithmetic
end
open WordOperations BinaryArithmetic
namespace NatOps

noncomputable def add {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)+value (g x)).bits) := by
  have hh := (hf.pair hg).comp BinaryArithmetic.add_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair,normalize_eq_bits,value_add,Bool.toNat_false,Nat.add_zero] using hh

noncomputable def sub {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)-value (g x)).bits) := by
  have hh := (hf.pair hg).comp BinarySubtraction.subtract_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair,
    normalize_eq_bits,BinarySubtraction.value_subtract] using hh

noncomputable def mul {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)*value (g x)).bits) := by
  have hh := (hf.pair hg).comp multiply_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair,normalize_mulFrom] using hh

noncomputable def div {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)/value (g x)).bits) := by
  have hh := ((hf.pair hg).comp BinaryDivision.divide_computes).comp extractPrefix_computes
  simp only [Function.comp_def,BinaryDivision.divide_pair] at hh
  simpa only [pairBits,extractPrefix_pair] using hh

noncomputable def mod {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)%value (g x)).bits) := BinaryGCD.mod_computes hf hg

noncomputable def gcd {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(Nat.gcd (value (f x)) (value (g x))).bits) := by
  have hh := (hf.pair hg).comp BinaryGCD.gcdWords_computes
  simpa only [Function.comp_def,BinaryGCD.gcdWords_pair] using hh

noncomputable def le {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>[decide (value (f x)≤value (g x))]) := by
  have hh := (hf.pair hg).comp BinarySubtraction.le_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def zero {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>[decide (value (f x)=0)]) := by
  have hh := hf.comp BinaryDivision.zeroTest_computes
  exact hh

end NatOps
namespace Signed

def encode (z : ℤ) : List Bool := decide (z<0)::z.natAbs.bits
def sign (x : List Bool) : Bool := x.head?.getD false
def mag (x : List Bool) : ℕ := value x.tail
def decode (x : List Bool) : ℤ := if sign x then -(mag x:ℤ) else (mag x:ℤ)
def pack (s : Bool) (x : List Bool) : List Bool :=
  if value x=0 then [false] else s::normalize x

def signed (s : Bool) (n : ℕ) : ℤ := if s then -(n:ℤ) else (n:ℤ)

lemma pack_bits (s : Bool) (n : ℕ) : pack s n.bits=encode (signed s n) := by
  simp only [pack,value_bits,normalize_eq_bits]
  cases s <;> by_cases hn : n=0 <;> simp [signed,encode,hn]; omega

lemma encode_decode (z : ℤ) : decode (encode z)=z := by
  simp only [decode,sign,encode,List.head?_cons,Option.getD_some,mag,List.tail_cons,value_bits,
    decide_eq_true_eq]
  split_ifs with h
  · exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt h)).symm
  · exact Int.natAbs_of_nonneg (le_of_not_gt h)

lemma encode_mag (z : ℤ) : mag (encode z)=z.natAbs := by
  simp only [mag,encode,List.tail_cons,value_bits]

noncomputable def sign_computes : PolyComputes (fun x=>[sign x]) := head_computes

noncomputable def pack_computes {s : List Bool → Bool} {f : List Bool → List Bool}
    (hs : PolyComputes (fun x=>[s x])) (hf : PolyComputes f) :
    PolyComputes (fun x=>pack (s x) (f x)) := by
  have hp := hs.append (hf.comp normalize_computes)
  have hh := (NatOps.zero hf).cond (const_computes [false]) hp
  simpa only [pack,Function.comp_def,List.singleton_append,decide_eq_true_eq] using hh

noncomputable def cast_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>encode (value (f x):ℤ)) := by
  have hh := pack_computes (const_computes [false]) (hf.comp normalize_computes)
  simpa only [Function.comp_def,normalize_eq_bits,pack_bits,signed,Bool.false_eq_true,ite_false] using hh

noncomputable def neg_computes : PolyComputes (fun x=>encode (-decode x)) := by
  have hm := tail_computes.comp normalize_computes
  have ha := pack_computes (const_computes [false]) hm
  have hb := pack_computes (const_computes [true]) hm
  have hh := sign_computes.cond ha hb
  have he : (fun x=>if sign x then pack false (normalize x.tail) else pack true (normalize x.tail)) =
      (fun x=>encode (-decode x)) := by
    funext x
    cases h : sign x <;> simp only [h,Bool.false_eq_true,ite_false,ite_true,normalize_eq_bits,pack_bits,signed,decode,mag,neg_neg]
  rw [← he]
  exact hh

lemma signed_add (s t : Bool) (a b : ℕ) :
    signed s a+signed t b =
    if s=t then signed s (a+b)
    else if a≤b then signed t (b-a) else signed s (a-b) := by
  cases s <;> cases t <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true,Bool.true_eq_false] <;>
    (try split_ifs) <;> omega

noncomputable def add_computes : PolyComputes (fun x=>
    encode (decode (extractPrefix x)+decode (discardPrefix x))) := by
  let l := extractPrefix_computes
  let r := discardPrefix_computes
  let sl := l.comp sign_computes
  let sr := r.comp sign_computes
  let al := l.comp tail_computes
  let ar := r.comp tail_computes
  have hs := NatOps.add al ar
  have hab := NatOps.sub al ar
  have hba := NatOps.sub ar al
  have hle := NatOps.le al ar
  have hdiff := hle.cond (pack_computes sr hba) (pack_computes sl hab)
  have hsum := pack_computes sl hs
  have ha := sr.cond hsum hdiff
  have hb := sr.cond hdiff hsum
  have hh := sl.cond ha hb
  have he (x : List Bool) :
      encode (decode (extractPrefix x)+decode (discardPrefix x)) =
      if sign (extractPrefix x) then
        if sign (discardPrefix x) then pack (sign (extractPrefix x)) (mag (extractPrefix x)+mag (discardPrefix x)).bits
        else if mag (extractPrefix x)≤ mag (discardPrefix x) then
          pack (sign (discardPrefix x)) (mag (discardPrefix x)-mag (extractPrefix x)).bits
        else pack (sign (extractPrefix x)) (mag (extractPrefix x)-mag (discardPrefix x)).bits
      else if sign (discardPrefix x) then
        if mag (extractPrefix x)≤ mag (discardPrefix x) then
          pack (sign (discardPrefix x)) (mag (discardPrefix x)-mag (extractPrefix x)).bits
        else pack (sign (extractPrefix x)) (mag (extractPrefix x)-mag (discardPrefix x)).bits
      else pack (sign (extractPrefix x)) (mag (extractPrefix x)+mag (discardPrefix x)).bits := by
    change encode (signed (sign (extractPrefix x)) _ + signed (sign (discardPrefix x)) _)=_
    rw [signed_add]
    cases hl : sign (extractPrefix x) <;> cases hr : sign (discardPrefix x) <;>
      simp only [Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,pack_bits] <;>
      (try split_ifs) <;> rfl
  simp_rw [he]
  convert hh using 1
  funext x
  dsimp [mag,Function.comp_def]
  simp only [decide_eq_true_eq]
  rfl

noncomputable def addition : Turing.TM2ComputableInPolyTime
    (fun p : ℤ×ℤ=>pairBits (encode p.1,encode p.2)) encode (fun p=>p.1+p.2) :=
  add_computes.reencode _ _ (fun p=>by
    simp only [pairBits,extractPrefix_pair,discardPrefix_pair,encode_decode])

end Signed
end MetricKMedianRecovery.BitMachine

end OAI
