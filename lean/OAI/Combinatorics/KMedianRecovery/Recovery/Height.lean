import Mathlib

namespace OAI

namespace MetricKMedianRecovery.RationalHeight
open scoped BigOperators

def Height (q : ℚ) (b : ℕ) : Prop := q.num.natAbs≤2^b ∧ q.den≤2^b

lemma Height.mono {q : ℚ} {b c : ℕ} (h : Height q b) (hc : b≤c) : Height q c :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by norm_num) hc),h.2.trans (Nat.pow_le_pow_right (by norm_num) hc)⟩

lemma zero (b : ℕ) : Height 0 b := by
  constructor
  · simp
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^b)

lemma of_fraction (p : ℤ) (d b : ℕ) (hd : 0<d) (hp : p.natAbs≤2^b) (hdb : d≤2^b) :
    Height ((p:ℚ)/(d:ℚ)) b := by
  constructor
  · by_cases hz : p=0
    · simp [hz]
    · have hh := Rat.num_dvd p (by exact_mod_cast hd.ne' : (d:ℤ)≠0)
      rw [←Rat.intCast_div_eq_divInt] at hh
      simp only [Int.cast_natCast] at hh
      exact (Nat.le_of_dvd (by omega : 0<p.natAbs) (Int.natAbs_dvd_natAbs.mpr hh)).trans hp
  · have hh := Rat.den_dvd p (d:ℤ)
    rw [←Rat.intCast_div_eq_divInt] at hh
    simp only [Int.cast_natCast] at hh
    exact (Nat.le_of_dvd hd (Int.natCast_dvd_natCast.mp hh)).trans hdb

lemma natCast (n b : ℕ) (hn : n≤2^b) : Height (n:ℚ) b := by
  constructor
  · simpa using hn
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^b)

lemma Height.neg {q : ℚ} {b : ℕ} (hq : Height q b) : Height (-q) b := by
  simpa only [Height,Rat.num_neg_eq_neg_num,Int.natAbs_neg,Rat.den_neg_eq_den] using hq

lemma Height.add {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q+r) (b+c+1) := by
  have hn : (q.num*(r.den:ℤ)+r.num*(q.den:ℤ)).natAbs≤2^(b+c+1) := by
    calc
      _ ≤ q.num.natAbs*r.den+r.num.natAbs*q.den := by
        simpa only [Int.natAbs_mul,Int.natAbs_natCast] using
          Int.natAbs_add_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ))
      _ ≤ 2^b*2^c+2^c*2^b := Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hr.1 hq.2)
      _ = _ := by rw [pow_succ,pow_add]; ring
  have hd : q.den*r.den≤2^(b+c+1) := by
    have hh := Nat.mul_le_mul hq.2 hr.2
    rw [←pow_add] at hh
    exact hh.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have he : q+r=((q.num*(r.den:ℤ)+r.num*(q.den:ℤ):ℤ):ℚ)/(q.den*r.den:ℕ) := by
    nth_rw 1 [←Rat.num_div_den q]
    nth_rw 1 [←Rat.num_div_den r]
    push_cast
    convert div_add_div (q.num:ℚ) (r.num:ℚ) (by exact_mod_cast q.den_nz : (q.den:ℚ)≠0) (by exact_mod_cast r.den_nz : (r.den:ℚ)≠0) using 1
    ring
  rw [he]
  exact of_fraction _ _ _ (Nat.mul_pos q.den_pos r.den_pos) hn hd

lemma Height.sub {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q-r) (b+c+1) := by
  rw [sub_eq_add_neg]
  exact hq.add hr.neg

lemma Height.mul {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q*r) (b+c) := by
  have hn : (q.num*r.num).natAbs≤2^(b+c) := by
    rw [Int.natAbs_mul,pow_add]
    exact Nat.mul_le_mul hq.1 hr.1
  have hd : q.den*r.den≤2^(b+c) := by rw [pow_add]; exact Nat.mul_le_mul hq.2 hr.2
  have he : q*r=((q.num*r.num:ℤ):ℚ)/(q.den*r.den:ℕ) := by
    nth_rw 1 [←Rat.num_div_den q]
    nth_rw 1 [←Rat.num_div_den r]
    push_cast
    exact div_mul_div_comm _ _ _ _
  rw [he]
  exact of_fraction _ _ _ (Nat.mul_pos q.den_pos r.den_pos) hn hd

lemma Height.inv {q : ℚ} {b : ℕ} (hq : Height q b) : Height q⁻¹ b := by
  by_cases hz : q=0
  · subst q
    simpa only [inv_zero] using zero b
  · have hn : q.num≠0 := Rat.num_ne_zero.mpr hz
    constructor
    · simpa only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_sign_of_ne_zero hn,
        Int.natAbs_natCast,one_mul] using hq.2
    · simpa only [Rat.den_inv_of_ne_zero hz] using hq.1

lemma Height.div {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q/r) (b+c) := by
  rw [div_eq_mul_inv]
  exact hq.mul hr.inv

lemma Height.pow {q : ℚ} {b : ℕ} (hq : Height q b) (k : ℕ) : Height (q^k) (k*b) := by
  induction k with
  | zero => simpa using natCast 1 0 (by norm_num)
  | succ k ih =>
    rw [pow_succ,Nat.succ_mul]
    exact ih.mul hq

lemma sum {V : Type*} [Fintype V] (f : V → ℚ) (b : ℕ) (hf : ∀ i,Height (f i) b) :
    Height (∑ i,f i) (Fintype.card V*(b+1)) := by
  have haux (s : Finset V) : Height (∑ i∈s,f i) (s.card*(b+1)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using zero 0
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha,Finset.card_insert_of_notMem ha]
      convert (hf a).add ih using 1
      ring
  simpa using haux Finset.univ

lemma sqrtFraction (p d D b e : ℕ) (hp : p≤2^b) (hd : d≤2^b) (hD : D≤2^e)
    (hd0 : 0<d) (hD0 : 0<D) :
    Height (((Nat.sqrt (p*d*D^2)+1:ℕ):ℚ)/(d*D:ℕ)) (2*b+2*e+1) := by
  have harg : p*d*D^2≤2^(2*b+2*e) := by
    calc
      _ ≤ 2^b*2^b*(2^e)^2 := Nat.mul_le_mul (Nat.mul_le_mul hp hd) (Nat.pow_le_pow_left hD 2)
      _ = _ := by rw [←pow_add,←pow_mul,←pow_add]; congr 1; omega
  have hs : Nat.sqrt (p*d*D^2)+1≤2^(2*b+2*e+1) := by
    have hh := (Nat.sqrt_le_self (p*d*D^2)).trans harg
    have ho : 1≤2^(2*b+2*e) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ 2^(2*b+2*e)+1 := Nat.add_le_add_right hh 1
      _ ≤ 2^(2*b+2*e)*2 := by omega
      _ = _ := (Nat.pow_succ 2 (2*b+2*e)).symm
  have hden : d*D≤2^(2*b+2*e+1) := by
    have hh := Nat.mul_le_mul hd hD
    rw [←pow_add] at hh
    exact hh.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  simpa only [Int.cast_natCast] using of_fraction ((Nat.sqrt (p*d*D^2)+1:ℕ):ℤ) (d*D) _
    (Nat.mul_pos hd0 hD0) (by simpa only [Int.natAbs_natCast] using hs) hden

end MetricKMedianRecovery.RationalHeight

end OAI
