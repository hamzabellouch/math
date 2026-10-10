import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.Reencode
import OAI.Combinatorics.KMedianRecovery.Recovery.Computes
import OAI.Combinatorics.KMedianRecovery.Machines.Program2

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryDivision
open BinaryArithmetic BinarySubtraction WordOperations

def pack (active : Bool) (digits divisor quotient remainder : List Bool) : List Bool :=
  active :: pairBits (digits, pairBits (divisor, pairBits (quotient,remainder)))
def digits (x : List Bool) := extractPrefix x.tail
def divisor (x : List Bool) := extractPrefix (discardPrefix x.tail)
def quotient (x : List Bool) := extractPrefix (discardPrefix (discardPrefix x.tail))
def remainder (x : List Bool) := discardPrefix (discardPrefix (discardPrefix x.tail))

@[simp] lemma decode_pack (a : Bool) (d y q r : List Bool) :
    digits (pack a d y q r)=d ∧ divisor (pack a d y q r)=y ∧
    quotient (pack a d y q r)=q ∧ remainder (pack a d y q r)=r := by
  simp only [digits,divisor,quotient,remainder,pack,List.tail_cons,pairBits,
    extractPrefix_pair,discardPrefix_pair,and_self]

@[simp] lemma digits_pack (a : Bool) (d y q r : List Bool) : digits (pack a d y q r)=d :=
  (decode_pack a d y q r).1
@[simp] lemma divisor_pack (a : Bool) (d y q r : List Bool) : divisor (pack a d y q r)=y :=
  (decode_pack a d y q r).2.1
@[simp] lemma quotient_pack (a : Bool) (d y q r : List Bool) : quotient (pack a d y q r)=q :=
  (decode_pack a d y q r).2.2.1
@[simp] lemma remainder_pack (a : Bool) (d y q r : List Bool) : remainder (pack a d y q r)=r :=
  (decode_pack a d y q r).2.2.2

lemma length_pack (a : Bool) (d y q r : List Bool) :
    (pack a d y q r).length=2*d.length+2*y.length+2*q.length+r.length+4 := by
  simp only [pack,List.length_cons,pairBits_length]
  omega

noncomputable def digits_computes : PolyComputes digits :=
  tail_computes.comp extractPrefix_computes
noncomputable def divisor_computes : PolyComputes divisor :=
  (tail_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def quotient_computes : PolyComputes quotient :=
  ((tail_computes.comp discardPrefix_computes).comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def remainder_computes : PolyComputes remainder :=
  ((tail_computes.comp discardPrefix_computes).comp discardPrefix_computes).comp discardPrefix_computes

noncomputable def pack_computes {d y q r : List Bool → List Bool}
    (a : Bool) (hd : PolyComputes d) (hy : PolyComputes y)
    (hq : PolyComputes q) (hr : PolyComputes r) :
    PolyComputes (fun x=>pack a (d x) (y x) (q x) (r x)) := by
  exact (const_computes [a]).append (hd.pair (hy.pair (hq.pair hr)))

def doubled (x : List Bool) : List Bool := (digits x).head?.getD false :: remainder x
def nextBit (x : List Bool) : Bool := decide (value (divisor x) ≤ value (doubled x))
def reduced (x : List Bool) : List Bool :=
  if nextBit x then normalize (subtract (doubled x) (divisor x)) else doubled x

def step (x : List Bool) : List Bool :=
  if digits x=[] then pack false [] (divisor x) (quotient x) (remainder x)
  else pack true (digits x).tail (divisor x) (nextBit x::quotient x) (reduced x)

noncomputable def doubled_computes : PolyComputes doubled := by
  exact (digits_computes.comp head_computes).append remainder_computes
noncomputable def nextBit_computes : PolyComputes (fun x=>[nextBit x]) := by
  have hh := (divisor_computes.pair doubled_computes).comp le_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair,nextBit] using hh
noncomputable def reduced_computes : PolyComputes reduced := by
  have hh := (doubled_computes.pair divisor_computes).comp subtract_computes
  simp only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] at hh
  exact nextBit_computes.cond hh doubled_computes
noncomputable def step_computes : PolyComputes step := by
  have ht := pack_computes true (digits_computes.comp tail_computes) divisor_computes
    (nextBit_computes.append quotient_computes) reduced_computes
  have hf := pack_computes false (const_computes []) divisor_computes quotient_computes remainder_computes
  have hh := (digits_computes.comp isEmpty_computes).cond hf ht
  change PolyComputes (fun xs=>if digits xs=[] then _ else _)
  simpa only [Function.comp_def,decide_eq_true_eq,List.singleton_append] using hh

lemma normalize_length (x : List Bool) : (normalize x).length ≤ x.length := by
  simpa only [BinaryArithmetic.normalize,List.length_reverse] using List.length_dropWhile_le (fun b:Bool=>!b) x.reverse
lemma subtract_length (x y : List Bool) : (subtract x y).length ≤ max x.length y.length := by
  dsimp only [subtract]
  split_ifs
  · simp
  · exact (difference_length false x y).le
lemma reduced_length (x : List Bool) :
    (reduced x).length ≤ (remainder x).length+(divisor x).length+1 := by
  have hn := normalize_length (subtract (doubled x) (divisor x))
  have hs := subtract_length (doubled x) (divisor x)
  have hd : (doubled x).length=(remainder x).length+1 := rfl
  rw [hd] at hs
  unfold reduced
  split_ifs
  · omega
  · simp only [doubled,List.length_cons]; omega

def mass (x : List Bool) : ℕ :=
  (digits x).length+(divisor x).length+(quotient x).length+(remainder x).length

def next := While.next step

def rank (x : List Bool) : ℕ := if x.head?=some true then (digits x).length+1 else 0

lemma divisor_next (x : List Bool) : divisor (next x)=divisor x := by
  unfold next While.next
  split_ifs
  · unfold step
    split_ifs <;> simp only [divisor_pack]
  · rfl

lemma mass_next (x : List Bool) : mass (next x) ≤ mass x+(divisor x).length+2 := by
  unfold next While.next
  split_ifs
  · unfold step
    split_ifs with h
    · simp only [mass,digits_pack,divisor_pack,quotient_pack,remainder_pack,List.length_nil]
      omega
    · have hr := reduced_length x
      simp only [mass,digits_pack,divisor_pack,quotient_pack,remainder_pack,List.length_cons,
        List.length_tail]
      omega
  · omega

lemma length_next (x : List Bool) :
    (next x).length ≤ max x.length (2*mass (next x)+4) := by
  unfold next While.next
  split_ifs
  · unfold step
    split_ifs <;> simp only [length_pack,mass,digits_pack,divisor_pack,quotient_pack,
      remainder_pack,List.length_nil,List.length_cons,List.length_tail] <;> omega
  · exact Nat.le_max_left _ _

lemma rank_next (x : List Bool) : rank (next x) ≤ rank x-1 := by
  unfold next While.next
  split_ifs with hx
  · unfold step
    split_ifs with hd
    · simp only [rank,pack,List.head?_cons,Option.some.injEq,Bool.false_eq_true,ite_false]
      exact Nat.zero_le _
    · have hh : (pack true (digits x).tail (divisor x) (nextBit x::quotient x) (reduced x)).head?=some true := rfl
      simp only [rank,hh,ite_true,digits_pack,hx,List.length_tail]
      have hp : 0<(digits x).length := List.length_pos_iff.mpr hd
      omega
  · simp only [rank,hx,ite_false,Nat.zero_sub,Nat.le_refl]

lemma projection_bounds (x : List Bool) :
    (digits x).length ≤ x.length ∧ (divisor x).length ≤ x.length ∧
    (quotient x).length ≤ x.length ∧ (remainder x).length ≤ x.length := by
  have h0 : x.tail.length ≤ x.length := by simp only [List.length_tail]; omega
  have h1 := ProductBits.projections_length x.tail
  have h2 := ProductBits.projections_length (discardPrefix x.tail)
  have h3 := ProductBits.projections_length (discardPrefix (discardPrefix x.tail))
  dsimp only [digits,divisor,quotient,remainder]
  omega

lemma rank_bound (x : List Bool) : rank x ≤ x.length+1 := by
  have h := (projection_bounds x).1
  unfold rank
  split_ifs <;> omega

lemma iterate_bounds (x : List Bool) (j : ℕ) :
    divisor (next^[j] x)=divisor x ∧
    mass (next^[j] x) ≤ mass x+j*((divisor x).length+2) ∧
    (next^[j] x).length ≤ x.length+2*mass x+2*j*((divisor x).length+2)+4 ∧
    rank (next^[j] x) ≤ rank x-j := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply,Nat.zero_mul,Nat.add_zero,Nat.sub_zero,
      Nat.le_refl,true_and,and_true]; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hd := divisor_next (next^[j] x)
    have hm := mass_next (next^[j] x)
    have hl := length_next (next^[j] x)
    have hr := rank_next (next^[j] x)
    rw [ih.1] at hd hm
    refine ⟨hd,?_,?_,?_⟩
    · nlinarith [ih.2.1]
    · apply hl.trans
      apply max_le
      · nlinarith [ih.2.2.1]
      · nlinarith [ih.2.1]
    · omega

lemma stop (x : List Bool) : (next^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds x (rank x)).2.2.2
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro hp
  change (if (next^[rank x] x).head?=some true then (digits (next^[rank x] x)).length+1 else 0)=0 at hh
  rw [ite_eq_left hp] at hh
  omega

noncomputable def loop_computes : PolyComputes (fun x=>next^[rank x] x) := by
  apply step_computes.whileLoop rank (Polynomial.X+1) (20*(Polynomial.X+1)^2)
  · intro x
    simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using rank_bound x
  · intro x j hj
    have hh := (iterate_bounds x j).2.2.1
    have hq := rank_bound x
    obtain ⟨hd,hy,hb,hr⟩ := projection_bounds x
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    change (next^[j] x).length ≤ _
    simp only [mass] at hh
    have hm : j*((divisor x).length+2) ≤ (x.length+1)*(x.length+2) :=
      Nat.mul_le_mul (hj.trans hq) (by omega)
    nlinarith
  · exact stop

end BinaryDivision
end MetricKMedianRecovery.BitMachine

end OAI
