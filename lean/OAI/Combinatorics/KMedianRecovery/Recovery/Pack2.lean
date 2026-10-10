import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DigitBit

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryGCD
open BinaryArithmetic BinarySubtraction WordOperations

def pack (active : Bool) (a b : List Bool) : List Bool := active::pairBits (a,b)
def first (x : List Bool) : List Bool := extractPrefix x.tail
def second (x : List Bool) : List Bool := discardPrefix x.tail
@[simp] lemma first_pack (c : Bool) (a b : List Bool) : first (pack c a b)=a :=
  extractPrefix_pair a b
@[simp] lemma second_pack (c : Bool) (a b : List Bool) : second (pack c a b)=b :=
  discardPrefix_pair a b
@[simp] lemma length_pack (c : Bool) (a b : List Bool) :
    (pack c a b).length=2*a.length+b.length+2 := by
  simp only [pack,List.length_cons,pairBits_length]
  omega

def firstRem (x : List Bool) : List Bool := (value (first x)%value (second x)).bits
def secondRem (x : List Bool) : List Bool :=
  (value (second x)%(value (first x)%value (second x))).bits

def step (x : List Bool) : List Bool :=
  if value (second x)=0 then pack false (normalize (first x)) []
  else if value (first x)%value (second x)=0 then pack false (normalize (second x)) []
  else pack true (firstRem x) (secondRem x)

noncomputable def first_computes : PolyComputes first := tail_computes.comp extractPrefix_computes
noncomputable def second_computes : PolyComputes second := tail_computes.comp discardPrefix_computes
noncomputable def pack_computes {f g : List Bool → List Bool} (b : Bool)
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (fun x=>pack b (f x) (g x)) :=
  (const_computes [b]).append (hf.pair hg)

noncomputable def mod_computes {f g : List Bool → List Bool}
    (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)%value (g x)).bits) := by
  have hh := ((hf.pair hg).comp BinaryDivision.divide_computes).comp discardPrefix_computes
  simp only [Function.comp_def,BinaryDivision.divide_pair] at hh
  simpa only [pairBits,discardPrefix_pair] using hh

noncomputable def firstRem_computes : PolyComputes firstRem := mod_computes first_computes second_computes
noncomputable def secondRem_computes : PolyComputes secondRem := by
  have hh := mod_computes second_computes firstRem_computes
  unfold secondRem
  simpa only [firstRem,value_bits] using hh

noncomputable def step_computes : PolyComputes step := by
  have ha := pack_computes false (first_computes.comp BinaryDivision.normalize_computes) (const_computes [])
  have hb := pack_computes false (second_computes.comp BinaryDivision.normalize_computes) (const_computes [])
  have hc := pack_computes true firstRem_computes secondRem_computes
  have hz := firstRem_computes.comp BinaryDivision.zeroTest_computes
  have hc' := hz.cond hb hc
  have hz' := second_computes.comp BinaryDivision.zeroTest_computes
  have hh := hz'.cond ha hc'
  change PolyComputes (fun x=>if value (second x)=0 then _ else if value (first x)%value (second x)=0 then _ else _)
  simpa only [Function.comp_def,firstRem,value_bits,decide_eq_true_eq] using hh

lemma modulus_twice_lt (a b : ℕ) (_ha : 0<a) (hb : 0<b) (hle : b ≤ a) : 2*(a%b)<a := by
  have hm := Nat.mod_lt a hb
  by_cases h : 2*b ≤ a
  · omega
  · have hd : a/b=1 := Nat.div_eq_of_lt_le (by simpa using hle) (by omega)
    have he := Nat.mod_add_div a b
    rw [hd,Nat.mul_one] at he
    omega

lemma size_drop_of_twice_lt (r a : ℕ) (h : 2*r<a) : r.size<a.size := by
  have ha : 0<a.size := Nat.size_pos.mpr (by omega)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have he := Nat.lt_size_self a
  rw [hk,pow_succ] at he
  have hr : r<2^k := by omega
  have hs := Nat.size_le.mpr hr
  omega

lemma second_mod_size_drop (a b : ℕ) (hb : 0<b) (hr : 0<a%b) :
    (a%b).size+(b%(a%b)).size<a.size+b.size := by
  have h1 := Nat.size_le_size (Nat.mod_le a b)
  have h2 := size_drop_of_twice_lt (b%(a%b)) b
    (modulus_twice_lt b (a%b) hb hr (Nat.le_of_lt (Nat.mod_lt a hb)))
  omega

def measure (x : List Bool) : ℕ := (value (first x)).size+(value (second x)).size
def rank (x : List Bool) : ℕ := if x.head?=some true then measure x+1 else 0
def Good (x : List Bool) : Prop := x.head?=some true ∨ value (second x)=0

def next := While.next step

@[simp] lemma measure_pack (c : Bool) (a b : List Bool) :
    measure (pack c a b)=(value a).size+(value b).size := by
  simp only [measure,first_pack,second_pack]
@[simp] lemma rank_true (a b : List Bool) : rank (pack true a b)=measure (pack true a b)+1 := rfl
@[simp] lemma rank_false (a b : List Bool) : rank (pack false a b)=0 := rfl

lemma step_bounds (x : List Bool) :
    measure (step x) ≤ measure x ∧ rank (step x) ≤ measure x ∧
    (step x).length ≤ 2*measure x+2 := by
  unfold step
  split_ifs with hy hz
  · simp only [measure_pack,normalize_eq_bits,value_bits,value,Nat.size_zero,Nat.add_zero,
      rank_false,length_pack,Nat.size_eq_bits_len,List.length_nil]
    simp only [measure]
    omega
  · simp only [measure_pack,normalize_eq_bits,value_bits,value,Nat.size_zero,Nat.add_zero,
      rank_false,length_pack,Nat.size_eq_bits_len,List.length_nil]
    simp only [measure]
    omega
  · have hh := second_mod_size_drop (value (first x)) (value (second x))
      (Nat.pos_of_ne_zero hy) (Nat.pos_of_ne_zero hz)
    simp only [rank_true,length_pack,firstRem,secondRem,measure,first_pack,second_pack,value_bits,Nat.size_eq_bits_len]
    omega

lemma gcd_step (x : List Bool) :
    Nat.gcd (value (first (step x))) (value (second (step x)))=
      Nat.gcd (value (first x)) (value (second x)) := by
  have h1 := Nat.gcd_rec (value (second x)) (value (first x))
  have h2 := Nat.gcd_rec (value (first x)%value (second x)) (value (second x))
  unfold step
  split_ifs with hy hz
  · simp only [first_pack,second_pack,normalize_eq_bits,value_bits,value,hy,Nat.gcd_zero_right]
  · simp only [first_pack,second_pack,normalize_eq_bits,value_bits,value,Nat.gcd_zero_right]
    rw [hz,Nat.gcd_zero_left] at h1
    exact h1.symm.trans (Nat.gcd_comm _ _)
  · simp only [first_pack,second_pack,firstRem,secondRem,value_bits]
    exact (Nat.gcd_comm _ _).trans (h2.symm.trans (h1.symm.trans (Nat.gcd_comm _ _)))

lemma step_good (x : List Bool) : Good (step x) := by
  unfold step
  split_ifs
  · exact Or.inr (by simp only [second_pack,value])
  · exact Or.inr (by simp only [second_pack,value])
  · exact Or.inl rfl

lemma next_bounds (x : List Bool) :
    measure (next x) ≤ measure x ∧ rank (next x) ≤ rank x-1 ∧
    (next x).length ≤ max x.length (2*measure x+2) := by
  unfold next While.next
  split_ifs with hx
  · have hh := step_bounds x
    change measure (step x) ≤ measure x ∧ rank (step x) ≤ (if x.head?=some true then measure x+1 else 0)-1 ∧ _
    rw [ite_eq_left hx]
    exact ⟨hh.1,by simpa using hh.2.1,hh.2.2.trans (Nat.le_max_right _ _)⟩
  · have hr : rank x=0 := ite_eq_right hx
    exact ⟨le_rfl,by simp only [hr,Nat.zero_sub,Nat.le_refl],Nat.le_max_left _ _⟩

lemma gcd_next (x : List Bool) :
    Nat.gcd (value (first (next x))) (value (second (next x)))=
      Nat.gcd (value (first x)) (value (second x)) := by
  unfold next While.next
  split_ifs
  · exact gcd_step x
  · rfl
lemma good_next (x : List Bool) (h : Good x) : Good (next x) := by
  unfold next While.next
  split_ifs
  · exact step_good x
  · exact h

lemma iterate_bounds (x : List Bool) (n : ℕ) :
    measure (next^[n] x) ≤ measure x ∧ rank (next^[n] x) ≤ rank x-n ∧
    (next^[n] x).length ≤ max x.length (2*measure x+2) := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply,Nat.sub_zero,Nat.le_refl,true_and]; exact Nat.le_max_left _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hh := next_bounds (next^[n] x)
    refine ⟨hh.1.trans ih.1,by omega,?_⟩
    apply hh.2.2.trans
    apply max_le ih.2.2
    apply le_trans _ (Nat.le_max_right _ _)
    omega

lemma measure_bound (x : List Bool) : measure x ≤ 2*x.length := by
  have ha := (ProductBits.projections_length x.tail).1
  have hb := (ProductBits.projections_length x.tail).2
  have hsa := Nat.size_le.mpr (BinarySubtraction.value_lt (first x))
  have hsb := Nat.size_le.mpr (BinarySubtraction.value_lt (second x))
  simp only [first,second] at hsa hsb
  simp only [List.length_tail] at ha hb
  simp only [measure,first,second]
  omega

lemma rank_bound (x : List Bool) : rank x ≤ 2*x.length+1 := by
  have hm := measure_bound x
  unfold rank
  split_ifs <;> omega
lemma stop (x : List Bool) : (next^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds x (rank x)).2.1
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro h
  change (if (next^[rank x] x).head?=some true then measure (next^[rank x] x)+1 else 0)=0 at hh
  rw [ite_eq_left h] at hh
  omega

noncomputable def loop_computes : PolyComputes (fun x=>next^[rank x] x) := by
  apply step_computes.whileLoop rank (2*Polynomial.X+1) (5*Polynomial.X+2)
  · intro x
    simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one] using rank_bound x
  · intro x j _
    have hh := (iterate_bounds x j).2.2
    have hm := measure_bound x
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    change (next^[j] x).length ≤ _
    apply hh.trans
    apply max_le <;> omega
  · exact stop

lemma loop_correct (a b : List Bool) :
    value (first (next^[rank (pack true a b)] (pack true a b)))=Nat.gcd (value a) (value b) := by
  have hh (n : ℕ) : Good (next^[n] (pack true a b)) ∧
      Nat.gcd (value (first (next^[n] (pack true a b))))
        (value (second (next^[n] (pack true a b))))=Nat.gcd (value a) (value b) := by
    induction n with
    | zero => exact ⟨Or.inl rfl,by simp only [Function.iterate_zero_apply,first_pack,second_pack]⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨good_next _ ih.1,(gcd_next _).trans ih.2⟩
  obtain ⟨hg,he⟩ := hh (rank (pack true a b))
  have hz := hg.resolve_left (stop (pack true a b))
  simpa only [hz,Nat.gcd_zero_right] using he

def gcdWords (x : List Bool) : List Bool :=
  normalize (first (next^[rank (pack true (extractPrefix x) (discardPrefix x))]
    (pack true (extractPrefix x) (discardPrefix x))))

noncomputable def gcdWords_computes : PolyComputes gcdWords := by
  have hi := pack_computes true extractPrefix_computes discardPrefix_computes
  have hl := hi.comp loop_computes
  have ht := first_computes.comp BinaryDivision.normalize_computes
  have hh := hl.comp ht
  unfold gcdWords
  simpa only [Function.comp_def] using hh

lemma gcdWords_pair (a b : List Bool) : gcdWords (pairBits (a,b))=(Nat.gcd (value a) (value b)).bits := by
  simp only [gcdWords,pairBits,extractPrefix_pair,discardPrefix_pair,normalize_eq_bits,loop_correct]

noncomputable def gcd : TM2ComputableInPolyTime
    (fun p : ℕ×ℕ=>pairBits (p.1.bits,p.2.bits)) Nat.bits (fun p=>Nat.gcd p.1 p.2) :=
  gcdWords_computes.reencode _ _ (fun p=>by simpa only [value_bits] using gcdWords_pair p.1.bits p.2.bits)

end BinaryGCD
end MetricKMedianRecovery.BitMachine

end OAI
