import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ProcessOutputs

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed

noncomputable def mul_computes : PolyComputes (fun x=>
    encode (decode (extractPrefix x)*decode (discardPrefix x))) := by
  let l := extractPrefix_computes
  let r := discardPrefix_computes
  let sl := l.comp sign_computes
  let sr := r.comp sign_computes
  let al := l.comp tail_computes
  let ar := r.comp tail_computes
  have hm := NatOps.mul al ar
  have hp := pack_computes (const_computes [false]) hm
  have hn := pack_computes (const_computes [true]) hm
  have hh := sl.cond (sr.cond hp hn) (sr.cond hn hp)
  convert hh using 1
  funext x
  dsimp only [Function.comp_def]
  cases hl : sign (extractPrefix x) <;> cases hr : sign (discardPrefix x) <;>
    simp only [decode,hl,hr,Bool.false_eq_true,ite_false,ite_true,pack_bits,signed,mag,
      Int.natCast_mul,neg_mul,mul_neg,neg_neg]

noncomputable def le_computes : PolyComputes (fun x=>
    [decide (decode (extractPrefix x)≤decode (discardPrefix x))]) := by
  let l := extractPrefix_computes
  let r := discardPrefix_computes
  let sl := l.comp sign_computes
  let sr := r.comp sign_computes
  let al := l.comp tail_computes
  let ar := r.comp tail_computes
  have hl := NatOps.le al ar
  have hr := NatOps.le ar al
  have hz := NatOps.zero (NatOps.add al ar)
  have hh := sl.cond (sr.cond hr (const_computes [true])) (sr.cond hz hl)
  convert hh using 1
  funext x
  dsimp only [Function.comp_def]
  cases h1 : sign (extractPrefix x) <;> cases h2 : sign (discardPrefix x) <;>
    simp only [decode,h1,h2,Bool.false_eq_true,ite_false,ite_true,mag,value_bits]
  all_goals congr 1; simp only [decide_eq_decide,decide_eq_true_eq]; omega

noncomputable def add {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>encode (decode (f x)+decode (g x))) := by
  have hh := (hf.pair hg).comp add_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def mul {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>encode (decode (f x)*decode (g x))) := by
  have hh := (hf.pair hg).comp mul_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def le {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>[decide (decode (f x)≤decode (g x))]) := by
  have hh := (hf.pair hg).comp le_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def neg {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>encode (-decode (f x))) := hf.comp neg_computes

noncomputable def subtraction : Turing.TM2ComputableInPolyTime
    (fun p : ℤ×ℤ=>pairBits (encode p.1,encode p.2)) encode (fun p=>p.1-p.2) := by
  have hh := add extractPrefix_computes (neg discardPrefix_computes)
  apply hh.reencode
  intro p
  simp only [pairBits,extractPrefix_pair,discardPrefix_pair,encode_decode,sub_eq_add_neg]

noncomputable def multiplication : Turing.TM2ComputableInPolyTime
    (fun p : ℤ×ℤ=>pairBits (encode p.1,encode p.2)) encode (fun p=>p.1*p.2) :=
  mul_computes.reencode _ _ (fun p=>by
    simp only [pairBits,extractPrefix_pair,discardPrefix_pair,encode_decode])

noncomputable def lessEqual : Turing.TM2ComputableInPolyTime
    (fun p : ℤ×ℤ=>pairBits (encode p.1,encode p.2)) (fun b:Bool=>[b]) (fun p=>decide (p.1≤p.2)) :=
  le_computes.reencode _ _ (fun p=>by
    simp only [pairBits,extractPrefix_pair,discardPrefix_pair,encode_decode])

@[simp] lemma natAbs_signed (s : Bool) (n : ℕ) : (signed s n).natAbs=n := by
  cases s <;> simp [signed]
lemma signed_div_nat (s : Bool) (n d : ℕ) (hd : d∣n) :
    signed s (n/d)=signed s n/(d:ℤ) := by
  cases s <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true,Int.natCast_ediv]
  rw [Int.neg_ediv_of_dvd (by exact_mod_cast hd)]

end Signed
namespace BinaryRational

def encode (x : ℚ) : List Bool := pairBits (Signed.encode x.num,x.den.bits)
def numerator (x : List Bool) : List Bool := extractPrefix x
def denominator (x : List Bool) : List Bool := discardPrefix x
def decode (x : List Bool) : ℚ := mkRat (Signed.decode (numerator x)) (value (denominator x))

lemma decode_encode (x : ℚ) : decode (encode x)=x := by
  simp only [decode,numerator,denominator,encode,pairBits,extractPrefix_pair,discardPrefix_pair,
    Signed.encode_decode,value_bits,Rat.mkRat_self]

def divisor (x : List Bool) : List Bool :=
  (Nat.gcd (Signed.mag (numerator x)) (value (denominator x))).bits

def reduceNonzero (x : List Bool) : List Bool :=
  pairBits (Signed.pack (Signed.sign (numerator x))
    (Signed.mag (numerator x)/value (divisor x)).bits,
    (value (denominator x)/value (divisor x)).bits)

def reduce (x : List Bool) : List Bool :=
  if value (denominator x)=0 then encode 0 else reduceNonzero x

noncomputable def numerator_computes : PolyComputes numerator := extractPrefix_computes
noncomputable def denominator_computes : PolyComputes denominator := discardPrefix_computes
noncomputable def divisor_computes : PolyComputes divisor := by
  unfold divisor Signed.mag
  exact NatOps.gcd (numerator_computes.comp tail_computes) denominator_computes

noncomputable def reduceNonzero_computes : PolyComputes reduceNonzero := by
  have hn := NatOps.div (numerator_computes.comp tail_computes) divisor_computes
  have hd := NatOps.div denominator_computes divisor_computes
  have hs := numerator_computes.comp Signed.sign_computes
  unfold reduceNonzero Signed.mag
  exact (Signed.pack_computes hs hn).pair hd

noncomputable def reduce_computes : PolyComputes reduce := by
  have hz := NatOps.zero denominator_computes
  have hh := hz.cond (const_computes (encode 0)) reduceNonzero_computes
  unfold reduce
  simpa only [decide_eq_true_eq] using hh

lemma reduce_correct (x : List Bool) : reduce x=encode (decode x) := by
  let s := Signed.sign (numerator x)
  let n := Signed.mag (numerator x)
  let d := value (denominator x)
  have hn : Signed.decode (numerator x)=Signed.signed s n := rfl
  by_cases hd : d=0
  · simp only [reduce,show value (denominator x)=0 from hd,ite_true,decode,Rat.mkRat_zero]
  · have hn' : (mkRat (Signed.signed s n) d).num=Signed.signed s (n/Nat.gcd n d) := by
      rw [Rat.num_mkRat,ite_eq_right hd,Signed.natAbs_signed,Nat.gcd_comm,
        Signed.signed_div_nat s n (Nat.gcd n d) (Nat.gcd_dvd_left n d)]
    have hd' : (mkRat (Signed.signed s n) d).den=d/Nat.gcd n d := by
      rw [Rat.den_mkRat,ite_eq_right hd,Signed.natAbs_signed,Nat.gcd_comm]
    change (if d=0 then _ else _)=_
    rw [ite_eq_right hd]
    simp only [reduceNonzero,divisor,value_bits]
    change pairBits (Signed.pack s (n/(Nat.gcd n d)).bits,(d/(Nat.gcd n d)).bits)=_
    rw [Signed.pack_bits]
    change _=pairBits (Signed.encode (mkRat (Signed.signed s n) d).num,
      (mkRat (Signed.signed s n) d).den.bits)
    rw [hn',hd']

noncomputable def normalize_computes : PolyComputes (fun x=>encode (decode x)) := by
  have he : reduce=(fun x=>encode (decode x)) := funext reduce_correct
  rw [← he]
  exact reduce_computes

noncomputable def normalize : Turing.TM2ComputableInPolyTime
    (fun p : ℤ×ℕ=>pairBits (Signed.encode p.1,p.2.bits)) encode (fun p=>mkRat p.1 p.2) :=
  normalize_computes.reencode _ _ (fun p=>by
    simp only [decode,numerator,denominator,pairBits,extractPrefix_pair,discardPrefix_pair,
      Signed.encode_decode,value_bits])

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
