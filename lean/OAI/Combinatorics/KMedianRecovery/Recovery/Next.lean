import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Copies

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinarySqrt

def next (n : ℕ) (s : ℕ×ℕ) : ℕ×ℕ :=
  let m := (s.1+s.2)/2
  if m*m≤n then (m,s.2) else (s.1,m)
def interval (n : ℕ) : ℕ → ℕ×ℕ
  | 0 => (0,n+1)
  | t+1 => next n (interval n t)
def Bracket (n : ℕ) (s : ℕ×ℕ) : Prop :=
  s.1<s.2 ∧ s.1*s.1≤n ∧ n<s.2*s.2 ∧ s.2≤n+1
lemma initial_bracket (n : ℕ) : Bracket n (0,n+1) := by
  simp only [Bracket]
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  · exact le_rfl
lemma next_bracket {n : ℕ} {s : ℕ×ℕ} (h : Bracket n s) : Bracket n (next n s) := by
  obtain ⟨l,u⟩ := s
  let m := (l+u)/2
  have hl : l ≤ m := by dsimp [m]; dsimp [Bracket] at h; omega
  have hu : m<u := by dsimp [m]; dsimp [Bracket] at h; omega
  change Bracket n (if m*m≤n then (m,u) else (l,m))
  split_ifs with hm
  · exact ⟨hu,hm,h.2.2.1,h.2.2.2⟩
  · have hlm : l < m := by nlinarith [h.2.1]
    exact ⟨hlm,h.2.1,Nat.lt_of_not_ge hm,hu.le.trans h.2.2.2⟩
lemma interval_bracket (n t : ℕ) : Bracket n (interval n t) := by
  induction t with
  | zero => exact initial_bracket n
  | succ t ih => exact next_bracket ih
lemma next_width {n : ℕ} {s : ℕ×ℕ} (h : s.1<s.2) :
    (next n s).2-(next n s).1-1≤(s.2-s.1-1)/2 := by
  obtain ⟨l,u⟩ := s
  dsimp only at h
  dsimp only [next]
  split_ifs <;> dsimp only <;> omega
lemma interval_width (n t : ℕ) : (interval n t).2-(interval n t).1-1≤n/2^t := by
  induction t with
  | zero => simp [interval]
  | succ t ih =>
    have hh := next_width (n:=n) (interval_bracket n t).1
    calc
      _ ≤ ((interval n t).2-(interval n t).1-1)/2 := hh
      _ ≤ (n/2^t)/2 := Nat.div_le_div_right ih
      _ = n/2^(t+1) := by rw [Nat.div_div_eq_div_mul,pow_succ]
lemma interval_correct (n t : ℕ) (ht : n.size≤t) : (interval n t).1=Nat.sqrt n := by
  have hb := interval_bracket n t
  have hw := interval_width n t
  have hn : n<2^t := Nat.size_le.mp ht
  rw [Nat.div_eq_of_lt hn] at hw
  have hl := Nat.le_sqrt.mpr hb.2.1
  have hu := Nat.sqrt_lt.mpr hb.2.2.1
  omega

def pack (n l u : ℕ) : List Bool := pairBits (n.bits,pairBits (l.bits,u.bits))
def low (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
def high (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
noncomputable def low_computes : PolyComputes low := discardPrefix_computes.comp extractPrefix_computes
noncomputable def high_computes : PolyComputes high := discardPrefix_computes.comp discardPrefix_computes

def middle (x : List Bool) : List Bool := ((value (low x)+value (high x))/2).bits
noncomputable def middle_computes : PolyComputes middle := by
  have hh := NatOps.div (NatOps.add low_computes high_computes) (const_computes (Nat.bits 2))
  change PolyComputes (fun x => ((value (low x)+value (high x))/2).bits)
  simpa only [value_bits] using hh

def leftCase (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (middle x,high x))
def rightCase (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (low x,middle x))
noncomputable def leftCase_computes : PolyComputes leftCase := extractPrefix_computes.pair
  (middle_computes.pair high_computes)
noncomputable def rightCase_computes : PolyComputes rightCase := extractPrefix_computes.pair
  (low_computes.pair middle_computes)
def step (x : List Bool) : List Bool :=
  if value (middle x)*value (middle x)≤value (extractPrefix x) then leftCase x else rightCase x
noncomputable def step_computes : PolyComputes step := by
  have hh := (NatOps.le (NatOps.mul middle_computes middle_computes) extractPrefix_computes).cond
    leftCase_computes rightCase_computes
  unfold step
  simpa only [value_bits,decide_eq_true_eq] using hh
lemma step_pack (n l u : ℕ) : step (pack n l u)=pack n (next n (l,u)).1 (next n (l,u)).2 := by
  simp only [step,middle,low,high,pack,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,
    leftCase,rightCase,next]
  split_ifs <;> rfl
lemma iterate_pack (n t : ℕ) : step^[t] (pack n 0 (n+1))=
    pack n (interval n t).1 (interval n t).2 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_pack]; rfl
lemma length_pack (n l u : ℕ) : (pack n l u).length=2*n.size+2*l.size+u.size+2 := by
  simp only [pack,pairBits_length,Nat.size_eq_bits_len]
  omega
lemma iterate_length (n t : ℕ) : (step^[t] (pack n 0 (n+1))).length≤5*n.size+5 := by
  rw [iterate_pack,length_pack]
  have hh := interval_bracket n t
  have hu : (interval n t).2.size≤n.size+1 := by
    have h := Nat.size_le_size (hh.2.2.2.trans (Nat.lt_size_self n))
    simpa only [Nat.size_pow] using h
  have hl := Nat.size_le_size hh.1.le
  omega

def startWords (x : List Bool) : List Bool := pairBits (x,pairBits ([],(value x+1).bits))
noncomputable def startWords_computes : PolyComputes startWords := by
  have hs := NatOps.add id_computes (const_computes (Nat.bits 1))
  have hh := id_computes.pair ((const_computes []).pair hs)
  change PolyComputes (fun x => pairBits (x,pairBits ([],(value x+1).bits)))
  simpa only [value_bits,id_eq] using hh
lemma startWords_bits (n : ℕ) : startWords n.bits=pack n 0 (n+1) := by
  simp only [startWords,value_bits,pack]
  rfl

noncomputable def run (x : List Bool) : List Bool :=
  low (BoundedIteration.polynomialRun step (Polynomial.X+1) (10*(Polynomial.X+1)) (startWords x))
noncomputable def run_computes : PolyComputes run :=
  (startWords_computes.comp (BoundedIteration.polynomialRun_computes step_computes
    (Polynomial.X+1) (10*(Polynomial.X+1)))).comp low_computes
lemma run_bits (n : ℕ) : run n.bits=(Nat.sqrt n).bits := by
  rw [run,startWords_bits,BoundedIteration.polynomialRun_eq]
  · rw [iterate_pack]
    simp only [low,pack,discardPrefix_pairBits,extractPrefix_pairBits]
    congr 1
    apply interval_correct
    have hp := length_pack n 0 (n+1)
    simp only [pack] at hp
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    omega
  · intro j _
    have hh := iterate_length n j
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,length_pack]
    omega
noncomputable def sqrt : Turing.TM2ComputableInPolyTime Nat.bits Nat.bits Nat.sqrt :=
  run_computes.reencode _ _ run_bits
end BinarySqrt
end MetricKMedianRecovery.BitMachine

end OAI
