import Mathlib
import OAI.Computability.MinUncut.Model

namespace OAI

namespace MinUncut.Preprocess
abbrev RawRat := ℕ × ℕ × ℕ
namespace RawRat

def value (q : RawRat) : ℚ := ((q.1:ℚ)-(q.2.1:ℚ))/((q.2.2:ℚ)+1)
def ofNat (n : ℕ) : RawRat := (n,0,0)
def neg (q : RawRat) : RawRat := (q.2.1,q.1,q.2.2)
def add (q r : RawRat) : RawRat :=
  (q.1*(r.2.2+1)+r.1*(q.2.2+1),q.2.1*(r.2.2+1)+r.2.1*(q.2.2+1),
    (q.2.2+1)*(r.2.2+1)-1)
def mul (q r : RawRat) : RawRat :=
  (q.1*r.1+q.2.1*r.2.1,q.1*r.2.1+q.2.1*r.1,(q.2.2+1)*(r.2.2+1)-1)
def inv (q : RawRat) : RawRat :=
  if q.1=q.2.1 then ofNat 0 else
  if q.2.1<q.1 then (q.2.2+1,0,q.1-q.2.1-1) else (0,q.2.2+1,q.2.1-q.1-1)
def le (q r : RawRat) : Prop :=
  q.1*(r.2.2+1)+r.2.1*(q.2.2+1)≤r.1*(q.2.2+1)+q.2.1*(r.2.2+1)
def lt (q r : RawRat) : Prop :=
  q.1*(r.2.2+1)+r.2.1*(q.2.2+1)<r.1*(q.2.2+1)+q.2.1*(r.2.2+1)
instance (q r : RawRat) : Decidable (le q r) := inferInstanceAs (Decidable (_≤_))
instance (q r : RawRat) : Decidable (lt q r) := inferInstanceAs (Decidable (_<_))

@[simp] lemma value_nat (n : ℕ) : (ofNat n).value=n := by simp [ofNat,value]
@[simp] lemma value_neg (q : RawRat) : q.neg.value = -q.value := by simp [neg,value]; ring
lemma product_denominator (a b : ℕ) : (((a+1)*(b+1)-1:ℕ):ℚ)+1=((a:ℚ)+1)*((b:ℚ)+1) := by
  have h : 1≤(a+1)*(b+1) := by nlinarith
  rw [Nat.cast_sub h]
  push_cast
  ring
@[simp] lemma value_add (q r : RawRat) : (add q r).value=q.value+r.value := by
  simp only [add,value,product_denominator]
  push_cast
  have hq : (q.2.2:ℚ)+1≠0 := by positivity
  have hr : (r.2.2:ℚ)+1≠0 := by positivity
  field_simp
  ring
@[simp] lemma value_mul (q r : RawRat) : (mul q r).value=q.value*r.value := by
  simp only [mul,value,product_denominator]
  push_cast
  rw [← mul_div_mul_comm]
  congr 1
  ring
@[simp] lemma value_inv (q : RawRat) : q.inv.value=q.value⁻¹ := by
  unfold inv
  by_cases h : q.1=q.2.1
  · simp [h,value,ofNat]
  · simp only [h,ite_false]
    by_cases hlt : q.2.1<q.1
    · rw [ite_eq_left hlt]
      have hsub : 1≤q.1-q.2.1 := by omega
      have hd : (((q.1-q.2.1-1:ℕ):ℚ)+1)=(q.1:ℚ)-q.2.1 := by
        rw [Nat.cast_sub hsub,Nat.cast_sub (by omega : q.2.1≤q.1)]
        simp
      simp only [value,hd,Nat.cast_zero,sub_zero,Nat.cast_add,Nat.cast_one,inv_div]
    · rw [ite_eq_right hlt]
      have hsub : 1≤q.2.1-q.1 := by omega
      have hd : (((q.2.1-q.1-1:ℕ):ℚ)+1)=(q.2.1:ℚ)-q.1 := by
        rw [Nat.cast_sub hsub,Nat.cast_sub (by omega : q.1≤q.2.1)]
        simp
      simp only [value,hd,Nat.cast_zero,zero_sub,Nat.cast_add,Nat.cast_one,inv_div]
      rw [show (q.1:ℚ)-q.2.1=-((q.2.1:ℚ)-q.1) by ring, div_neg, neg_div]

lemma le_iff (q r : RawRat) : le q r ↔ q.value≤r.value := by
  unfold le value
  rw [div_le_div_iff₀ (by positivity : (0:ℚ)<q.2.2+1) (by positivity : (0:ℚ)<r.2.2+1)]
  have hc : q.1*(r.2.2+1)+r.2.1*(q.2.2+1)≤r.1*(q.2.2+1)+q.2.1*(r.2.2+1) ↔
      (q.1:ℚ)*(r.2.2+1)+(r.2.1:ℚ)*(q.2.2+1)≤(r.1:ℚ)*(q.2.2+1)+(q.2.1:ℚ)*(r.2.2+1) := by
    exact_mod_cast Iff.rfl
  rw [hc]
  constructor <;> intro h <;> nlinarith
lemma lt_iff (q r : RawRat) : lt q r ↔ q.value<r.value := by
  unfold lt value
  rw [div_lt_div_iff₀ (by positivity : (0:ℚ)<q.2.2+1) (by positivity : (0:ℚ)<r.2.2+1)]
  have hc : q.1*(r.2.2+1)+r.2.1*(q.2.2+1)<r.1*(q.2.2+1)+q.2.1*(r.2.2+1) ↔
      (q.1:ℚ)*(r.2.2+1)+(r.2.1:ℚ)*(q.2.2+1)<(r.1:ℚ)*(q.2.2+1)+(q.2.1:ℚ)*(r.2.2+1) := by
    exact_mod_cast Iff.rfl
  rw [hc]
  constructor <;> intro h <;> nlinarith

end RawRat

lemma primrec_pow : Primrec₂ (fun a n : ℕ=>a^n) := by
  have h : Primrec₂ (fun a n : ℕ=> Nat.rec (motive := fun _ => ℕ) 1 (fun _ r=>r*a) n) :=
    Primrec.nat_rec (Primrec.const 1) ((Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂)
  apply h.of_eq
  intro a n
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih,pow_succ]

lemma primrec_factorial : Primrec Nat.factorial := by
  have h : Primrec (Nat.rec 1 (fun n r=> (n+1)*r)) :=
    Primrec.nat_rec₁ 1 ((Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂)
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih,Nat.factorial_succ]

lemma choose_factorial (n k : ℕ) : n.choose k =
    if k≤n then n.factorial/(k.factorial*(n-k).factorial) else 0 := by
  by_cases h : k≤n
  · rw [ite_eq_left h]
    exact Nat.choose_eq_factorial_div_factorial h
  · rw [ite_eq_right h,Nat.choose_eq_zero_of_lt (by omega : n<k)]

lemma primrec_choose : Primrec₂ Nat.choose := by
  have h : Primrec (fun p : ℕ × ℕ=>if p.2≤p.1 then
      p.1.factorial/(p.2.factorial*(p.1-p.2).factorial) else 0) :=
    Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
      (Primrec.nat_div.comp (primrec_factorial.comp Primrec.fst)
        (Primrec.nat_mul.comp (primrec_factorial.comp Primrec.snd)
          (primrec_factorial.comp Primrec.nat_sub))) (Primrec.const 0)
  exact h.to₂.of_eq (fun n k=>(choose_factorial n k).symm)

namespace RawRat

lemma primrec_ofNat : Primrec ofNat := Primrec.id.pair ((Primrec.const 0).pair (Primrec.const 0))
lemma primrec_neg : Primrec neg :=
  (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))

lemma primrec_add : Primrec₂ add := by
  let p : Primrec (fun q : RawRat × RawRat => q.1.1) := Primrec.fst.comp Primrec.fst
  let n : Primrec (fun q : RawRat × RawRat => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  let d : Primrec (fun q : RawRat × RawRat => q.1.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  let p' : Primrec (fun q : RawRat × RawRat => q.2.1) := Primrec.fst.comp Primrec.snd
  let n' : Primrec (fun q : RawRat × RawRat => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let d' : Primrec (fun q : RawRat × RawRat => q.2.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp p d') (Primrec.nat_mul.comp p' d)).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp n d') (Primrec.nat_mul.comp n' d)).pair
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp d d') (Primrec.const 1)))).to₂

lemma primrec_mul : Primrec₂ mul := by
  let p : Primrec (fun q : RawRat × RawRat => q.1.1) := Primrec.fst.comp Primrec.fst
  let n : Primrec (fun q : RawRat × RawRat => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  let d : Primrec (fun q : RawRat × RawRat => q.1.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  let p' : Primrec (fun q : RawRat × RawRat => q.2.1) := Primrec.fst.comp Primrec.snd
  let n' : Primrec (fun q : RawRat × RawRat => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let d' : Primrec (fun q : RawRat × RawRat => q.2.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp p p') (Primrec.nat_mul.comp n n')).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp p n') (Primrec.nat_mul.comp n p')).pair
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp d d') (Primrec.const 1)))).to₂

lemma primrec_inv : Primrec inv := by
  let p : Primrec (fun q : RawRat => q.1) := Primrec.fst
  let n : Primrec (fun q : RawRat => q.2.1) := Primrec.fst.comp Primrec.snd
  let d : Primrec (fun q : RawRat => q.2.2+1) := Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.ite (Primrec.eq.comp p n) (Primrec.const (ofNat 0))
    (Primrec.ite (Primrec.nat_lt.comp n p)
      (d.pair ((Primrec.const 0).pair (Primrec.nat_sub.comp (Primrec.nat_sub.comp p n) (Primrec.const 1))))
      ((Primrec.const 0).pair (d.pair (Primrec.nat_sub.comp (Primrec.nat_sub.comp n p) (Primrec.const 1)))))

lemma primrec_le : PrimrecRel le := by

  let p : Primrec (fun q : RawRat × RawRat => q.1.1) := Primrec.fst.comp Primrec.fst
  let n : Primrec (fun q : RawRat × RawRat => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  let d : Primrec (fun q : RawRat × RawRat => q.1.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  let p' : Primrec (fun q : RawRat × RawRat => q.2.1) := Primrec.fst.comp Primrec.snd
  let n' : Primrec (fun q : RawRat × RawRat => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let d' : Primrec (fun q : RawRat × RawRat => q.2.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.nat_le.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp p d') (Primrec.nat_mul.comp n' d))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp p' d) (Primrec.nat_mul.comp n d'))

lemma primrec_lt : PrimrecRel lt := by
  let p : Primrec (fun q : RawRat × RawRat => q.1.1) := Primrec.fst.comp Primrec.fst
  let n : Primrec (fun q : RawRat × RawRat => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  let d : Primrec (fun q : RawRat × RawRat => q.1.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  let p' : Primrec (fun q : RawRat × RawRat => q.2.1) := Primrec.fst.comp Primrec.snd
  let n' : Primrec (fun q : RawRat × RawRat => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let d' : Primrec (fun q : RawRat × RawRat => q.2.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.nat_lt.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp p d') (Primrec.nat_mul.comp n' d))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp p' d) (Primrec.nat_mul.comp n d'))

def pow (q : RawRat) : ℕ → RawRat
  | 0 => ofNat 1
  | n+1 => mul (pow q n) q
@[simp] lemma value_pow (q : RawRat) (n : ℕ) : (pow q n).value=q.value^n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp only [pow,value_mul,ih,pow_succ]
lemma primrec_pow : Primrec₂ pow := by
  have h : Primrec₂ (fun q n => Nat.rec (motive:=fun _=>RawRat) (ofNat 1) (fun _ r=>mul r q) n) :=
    Primrec.nat_rec (Primrec.const (ofNat 1)) ((primrec_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂)
  apply h.of_eq
  intro q n
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih,pow]

def ceil (q : RawRat) : ℕ := (q.1-q.2.1+q.2.2)/(q.2.2+1)
lemma primrec_ceil : Primrec ceil :=
  Primrec.nat_div.comp
    (Primrec.nat_add.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd))
    (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))

end RawRat
end MinUncut.Preprocess

namespace MinUncut.Preprocess.RawRat
lemma ceil_eq (q : RawRat) : q.ceil=⌈q.value⌉₊ := by
  apply Nat.le_antisymm
  · unfold ceil
    rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0<q.2.2+1)]
    have h := Nat.le_ceil q.value
    rw [value,div_le_iff₀ (by positivity : (0:ℚ)<q.2.2+1)] at h
    change (q.1:ℚ)-q.2.1≤(⌈q.value⌉₊:ℚ)*(q.2.2+1) at h
    have hn : q.1-q.2.1≤(q.2.2+1)*⌈q.value⌉₊ := by
      by_cases hp : q.2.1≤q.1
      · have he : ((q.1-q.2.1:ℕ):ℚ)≤((q.2.2+1)*⌈q.value⌉₊:ℕ) := by
          rw [Nat.cast_sub hp]
          push_cast
          nlinarith
        exact_mod_cast he
      · have he : q.1-q.2.1=0 := by omega
        rw [he]; exact Nat.zero_le _
    omega
  · apply Nat.ceil_le.mpr
    rw [value,div_le_iff₀ (by positivity : (0:ℚ)<q.2.2+1)]
    have hm := Nat.mod_lt (q.1-q.2.1+q.2.2) (by omega : 0<q.2.2+1)
    have he := Nat.div_add_mod (q.1-q.2.1+q.2.2) (q.2.2+1)
    have hn : q.1-q.2.1≤(q.2.2+1)*q.ceil := by unfold ceil; omega
    have hh : (q.1:ℚ)-q.2.1≤(q.1-q.2.1:ℕ) := by
      by_cases hp : q.2.1≤q.1
      · rw [Nat.cast_sub hp]
      · have hq : q.1≤q.2.1 := by omega
        have hq' : (q.1:ℚ)≤q.2.1 := by exact_mod_cast hq
        exact le_trans (sub_nonpos.mpr hq') (by positivity)
    have hn' : ((q.1-q.2.1:ℕ):ℚ)≤((q.2.2+1)*q.ceil:ℕ) := by exact_mod_cast hn
    push_cast at hn'
    nlinarith

def represent (q : ℚ) : RawRat := (q.num.toNat,(-q.num).toNat,q.den-1)
@[simp] lemma value_represent (q : ℚ) : (represent q).value=q := by
  have hp : 1≤q.den := Rat.den_pos q
  have hd : ((q.den-1:ℕ):ℚ)+1=q.den := by rw [Nat.cast_sub hp]; simp
  unfold value represent
  dsimp only
  rw [hd]
  have hn : (q.num.toNat:ℚ)-(-q.num).toNat=q.num := by
    exact_mod_cast Int.toNat_sub_toNat_neg q.num
  rw [hn,Rat.num_div_den]
end MinUncut.Preprocess.RawRat

namespace MinUncut.Preprocess

lemma primrec_gcd : Primrec₂ Nat.gcd := by
  have hd : PrimrecRel (fun a b : ℕ=>a ∣ b) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).of_eq
      (by intro p; exact Nat.dvd_iff_mod_eq_zero.symm)
  have hf : Primrec (fun p : ℕ × ℕ => Nat.findGreatest (fun k=>k∣p.1 ∧ k∣p.2) p.2) :=
    Primrec.nat_findGreatest Primrec.snd
      ((hd.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).and
       (hd.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
  apply (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) Primrec.fst hf).to₂.of_eq
  intro m n
  by_cases hn : n=0
  · simp [hn]
  · simp only [hn,ite_false]
    have hgn : m.gcd n≤n := Nat.gcd_le_right m (by omega)
    have hdvd : (Nat.findGreatest (fun k=>k∣m ∧ k∣n) n) ∣ m.gcd n := by
      have hh := Nat.findGreatest_spec (P:=fun k=>k∣m ∧ k∣n) hgn ⟨Nat.gcd_dvd_left m n,Nat.gcd_dvd_right m n⟩
      exact Nat.dvd_gcd hh.1 hh.2
    apply Nat.le_antisymm
    · exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_right m (by omega)) hdvd
    · exact Nat.le_findGreatest hgn ⟨Nat.gcd_dvd_left m n,Nat.gcd_dvd_right m n⟩

lemma primrec_intCode : Primrec (Equiv.intEquivNat : ℤ → ℕ) := Primrec.encode

lemma intCode_nat (n : ℕ) : Equiv.intEquivNat (Int.ofNat n)=2*n := by
  rfl
lemma intCode_negSucc (n : ℕ) : Equiv.intEquivNat (Int.negSucc n)=2*n+1 := by
  simp [Equiv.intEquivNat,Equiv.intEquivNatSumNat]

lemma primrec_intAbs : Primrec Int.natAbs := by
  apply (Primrec.nat_div.comp (Primrec.succ.comp primrec_intCode) (Primrec.const 2)).of_eq
  intro z
  cases z with
  | ofNat n => rw [intCode_nat]; change (2*n).succ/2=n; omega
  | negSucc n => rw [intCode_negSucc]; simp only [Int.natAbs_negSucc]; omega

lemma primrec_intToNat : Primrec Int.toNat := by
  apply (Primrec.ite (Primrec.eq.comp
      (Primrec.nat_mod.comp primrec_intCode (Primrec.const 2)) (Primrec.const 0))
      (Primrec.nat_div.comp primrec_intCode (Primrec.const 2)) (Primrec.const 0)).of_eq
  intro z
  cases z with
  | ofNat n => rw [intCode_nat]; simp
  | negSucc n => rw [intCode_negSucc]; simp

lemma primrec_intNegToNat : Primrec (fun z : ℤ=>(-z).toNat) := by
  apply (Primrec.ite (Primrec.eq.comp
      (Primrec.nat_mod.comp primrec_intCode (Primrec.const 2)) (Primrec.const 0))
      (Primrec.const 0)
      (Primrec.succ.comp (Primrec.nat_div.comp primrec_intCode (Primrec.const 2)))).of_eq
  intro z
  cases z with
  | ofNat n => rw [intCode_nat]; simp
  | negSucc n => rw [intCode_negSucc]; simp; omega

abbrev RationalPair := {p : ℤ × ℕ // 0<p.2 ∧ p.1.natAbs.Coprime p.2}
lemma rationalPair_prim : PrimrecPred (fun p : ℤ × ℕ=>0<p.2 ∧ p.1.natAbs.Coprime p.2) := by
  exact (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and
    ((Primrec.eq.comp (primrec_gcd.comp (primrec_intAbs.comp Primrec.fst) Primrec.snd)
      (Primrec.const 1)).of_eq (by intro p; rfl))

instance rationalPairPrimcodable : Primcodable RationalPair := Primcodable.subtype rationalPair_prim

def rationalEquiv : ℚ ≃ RationalPair where
  toFun q := ⟨(q.num,q.den),Rat.den_pos q,q.reduced⟩
  invFun p := ⟨p.val.1,p.val.2,by exact Nat.ne_of_gt p.prop.1,p.prop.2⟩
  left_inv q := rfl
  right_inv p := rfl

instance rationalPrimcodable : Primcodable ℚ := Primcodable.ofEquiv RationalPair rationalEquiv

lemma primrec_ratNum : Primrec Rat.num :=
  Primrec.fst.comp (Primrec.subtype_val.comp (Primrec.of_equiv (e:=rationalEquiv)))
lemma primrec_ratDen : Primrec Rat.den :=
  Primrec.snd.comp (Primrec.subtype_val.comp (Primrec.of_equiv (e:=rationalEquiv)))
lemma primrec_represent : Primrec RawRat.represent :=
  (primrec_intToNat.comp primrec_ratNum).pair
    ((primrec_intNegToNat.comp primrec_ratNum).pair
      (Primrec.nat_sub.comp primrec_ratDen (Primrec.const 1)))

open Encodable
local instance : Encodable ℚ := rationalPrimcodable.toEncodable

def candidate (q : RawRat) (n : ℕ) : Option ℚ :=
  (decode n).filter (fun r=>decide (RawRat.le q (RawRat.represent r) ∧ RawRat.le (RawRat.represent r) q))

lemma candidate_eq {q : RawRat} {n : ℕ} {r : ℚ} (h : r ∈ candidate q n) : r=q.value := by
  have hh : RawRat.le q (RawRat.represent r) ∧ RawRat.le (RawRat.represent r) q := by
    cases hn : decode (α:=ℚ) n with
    | none => simp [candidate,hn] at h
    | some s =>
      have ht : s=r ∧ RawRat.le q (RawRat.represent r) ∧ RawRat.le (RawRat.represent r) q := by
        simpa [candidate,hn] using h
      exact ht.2
  have h₁ := (RawRat.le_iff q (RawRat.represent r)).mp hh.1
  have h₂ := (RawRat.le_iff (RawRat.represent r) q).mp hh.2
  simpa only [RawRat.value_represent] using le_antisymm h₂ h₁

lemma candidate_exists (q : RawRat) : ∃ n, q.value ∈ candidate q n := by
  refine ⟨encode q.value,?_⟩
  simp only [candidate,encodek,Option.filter_some,Option.mem_def]
  have h₁ : RawRat.le q (RawRat.represent q.value) := by
    rw [RawRat.le_iff,RawRat.value_represent]
  have h₂ : RawRat.le (RawRat.represent q.value) q := by
    rw [RawRat.le_iff,RawRat.value_represent]
  simp [h₁,h₂]

lemma candidate_primrec : Primrec₂ candidate := by
  have hc : PrimrecPred (fun p : RawRat × ℚ=> RawRat.le p.1 (RawRat.represent p.2) ∧
      RawRat.le (RawRat.represent p.2) p.1) :=
    (RawRat.primrec_le.comp Primrec.fst (primrec_represent.comp Primrec.snd)).and
      (RawRat.primrec_le.comp (primrec_represent.comp Primrec.snd) Primrec.fst)
  apply (Primrec.option_bind (Primrec.decode.comp Primrec.snd)
    (Primrec.ite (hc.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂).to₂.of_eq
  intro q n
  unfold candidate
  cases decode (α:=ℚ) n <;> simp [Option.filter]

lemma computable_value : Computable RawRat.value := by
  apply (Partrec.rfindOpt candidate_primrec.to_comp).of_eq
  intro q
  apply Part.eq_some_iff.mpr
  obtain ⟨n,hn⟩ := candidate_exists q
  have hd := Nat.rfindOpt_dom.mpr ⟨n,q.value,hn⟩
  obtain ⟨r,hr⟩ := Part.dom_iff_mem.mp hd
  obtain ⟨m,hm⟩ := Nat.rfindOpt_spec hr
  rw [candidate_eq hm] at hr
  exact hr

lemma computable_ratAdd : Computable₂ (fun q r : ℚ=>q+r) := by
  have h : Computable (fun p : ℚ × ℚ=>RawRat.add (RawRat.represent p.1) (RawRat.represent p.2)) :=
    RawRat.primrec_add.to_comp.comp (primrec_represent.to_comp.comp Computable.fst)
      (primrec_represent.to_comp.comp Computable.snd)
  exact (computable_value.comp h).of_eq (by intro p; simp only [RawRat.value_add,RawRat.value_represent])
lemma computable_ratMul : Computable₂ (fun q r : ℚ=>q*r) := by
  have h : Computable (fun p : ℚ × ℚ=>RawRat.mul (RawRat.represent p.1) (RawRat.represent p.2)) :=
    RawRat.primrec_mul.to_comp.comp (primrec_represent.to_comp.comp Computable.fst)
      (primrec_represent.to_comp.comp Computable.snd)
  exact (computable_value.comp h).of_eq (by intro p; simp only [RawRat.value_mul,RawRat.value_represent])
lemma computable_ratNeg : Computable (fun q : ℚ=>-q) := by
  exact (computable_value.comp (RawRat.primrec_neg.to_comp.comp primrec_represent.to_comp)).of_eq
    (by intro q; simp only [RawRat.value_neg,RawRat.value_represent])
lemma computable_ratInv : Computable (fun q : ℚ=>q⁻¹) := by
  exact (computable_value.comp (RawRat.primrec_inv.to_comp.comp primrec_represent.to_comp)).of_eq
    (by intro q; simp only [RawRat.value_inv,RawRat.value_represent])
lemma computable_ratSub : Computable₂ (fun q r : ℚ=>q-r) :=
  (computable_ratAdd.comp Computable.fst (computable_ratNeg.comp Computable.snd)).of_eq
    (by intro p; exact (sub_eq_add_neg p.1 p.2).symm)
lemma computable_ratDiv : Computable₂ (fun q r : ℚ=>q/r) :=
  (computable_ratMul.comp Computable.fst (computable_ratInv.comp Computable.snd)).of_eq
    (by intro p; exact (div_eq_mul_inv p.1 p.2).symm)
lemma computable_ratPow : Computable₂ (fun (q : ℚ) (n : ℕ)=>q^n) := by
  have h : Computable (fun p : ℚ × ℕ=>RawRat.pow (RawRat.represent p.1) p.2) :=
    RawRat.primrec_pow.to_comp.comp (primrec_represent.to_comp.comp Computable.fst) Computable.snd
  exact (computable_value.comp h).of_eq (by intro p; simp only [RawRat.value_pow,RawRat.value_represent])
lemma computable_ratNat : Computable (fun n : ℕ=>(n:ℚ)) :=
  (computable_value.comp RawRat.primrec_ofNat.to_comp).of_eq (by intro n; simp only [RawRat.value_nat])
lemma primrec_ratLe : PrimrecRel (fun q r : ℚ=>q≤r) :=
  (RawRat.primrec_le.comp (primrec_represent.comp Primrec.fst)
    (primrec_represent.comp Primrec.snd)).of_eq (by intro p; simp [RawRat.le_iff])
lemma primrec_ratLt : PrimrecRel (fun q r : ℚ=>q<r) :=
  (RawRat.primrec_lt.comp (primrec_represent.comp Primrec.fst)
    (primrec_represent.comp Primrec.snd)).of_eq (by intro p; simp [RawRat.lt_iff])
lemma primrec_ratCeil : Primrec (fun q : ℚ=>⌈q⌉₊) :=
  (RawRat.primrec_ceil.comp primrec_represent).of_eq (by intro q; rw [RawRat.ceil_eq,RawRat.value_represent])

end MinUncut.Preprocess

section
attribute [fun_prop] Computable ComputablePred

namespace MinUncut.Preprocess
variable {α : Type} [Primcodable α]

@[fun_prop] lemma ca_id : Computable (fun a : α=>a) := Computable.id
@[fun_prop] lemma ca_const {β : Type} [Primcodable β] (b : β) : Computable (fun _ : α=>b) := Computable.const b
@[fun_prop] lemma ca_fst {β : Type} [Primcodable β] : Computable (Prod.fst : α × β → α) := Computable.fst
@[fun_prop] lemma ca_snd {β : Type} [Primcodable β] : Computable (Prod.snd : α × β → β) := Computable.snd
@[fun_prop] lemma ca_comp {β γ : Type} [Primcodable β] [Primcodable γ] {g : β → γ} {f : α → β}
    (hg : Computable g) (hf : Computable f) : Computable (fun x=>g (f x)) := hg.comp hf
@[fun_prop] lemma ca_pair {β γ : Type} [Primcodable β] [Primcodable γ] {f : α → β} {g : α → γ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x=>(f x,g x)) := hf.pair hg
@[fun_prop] lemma ca_add {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x+g x) :=
  Primrec.nat_add.to_comp.comp hf hg
@[fun_prop] lemma ca_sub {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x-g x) :=
  Primrec.nat_sub.to_comp.comp hf hg
@[fun_prop] lemma ca_mul {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x*g x) :=
  Primrec.nat_mul.to_comp.comp hf hg
@[fun_prop] lemma ca_pow {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x^g x) :=
  primrec_pow.to_comp.comp hf hg
@[fun_prop] lemma ca_div {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x/g x) :=
  Primrec.nat_div.to_comp.comp hf hg
@[fun_prop] lemma ca_mod {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x%g x) :=
  Primrec.nat_mod.to_comp.comp hf hg
@[fun_prop] lemma ca_choose {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>(f x).choose (g x)) :=
  primrec_choose.to_comp.comp hf hg
@[fun_prop] lemma ca_factorial {f : α → ℕ} (hf : Computable f) : Computable (fun x=>(f x).factorial) :=
  primrec_factorial.to_comp.comp hf
@[fun_prop] lemma ca_ratCast {f : α → ℕ} (hf : Computable f) : Computable (fun x=>(f x:ℚ)) :=
  computable_ratNat.comp hf
@[fun_prop] lemma ca_ratAdd {f g : α → ℚ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x+g x) := computable_ratAdd.comp hf hg
@[fun_prop] lemma ca_ratSub {f g : α → ℚ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x-g x) := computable_ratSub.comp hf hg
@[fun_prop] lemma ca_ratMul {f g : α → ℚ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x*g x) := computable_ratMul.comp hf hg
@[fun_prop] lemma ca_ratDiv {f g : α → ℚ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x/g x) := computable_ratDiv.comp hf hg
@[fun_prop] lemma ca_ratInv {f : α → ℚ} (hf : Computable f) : Computable (fun x=>(f x)⁻¹) := computable_ratInv.comp hf
@[fun_prop] lemma ca_ratPow {f : α → ℚ} {g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x^g x) := computable_ratPow.comp hf hg
@[fun_prop] lemma ca_ratCeil {f : α → ℚ} (hf : Computable f) : Computable (fun x=>⌈f x⌉₊) := primrec_ratCeil.to_comp.comp hf

@[fun_prop] lemma ca_and {p q : α → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun x=>p x ∧ q x) := by
  rcases hp with ⟨dp,hp⟩
  rcases hq with ⟨dq,hq⟩
  apply Computable.computablePred
  exact (Primrec.and.to_comp.comp hp hq).of_eq (by intro x; simp)
@[fun_prop] lemma ca_natLe {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun x=>f x≤g x) :=
  (Primrec.nat_le.computablePred.decide.comp (hf.pair hg)).computablePred
@[fun_prop] lemma ca_natLt {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun x=>f x<g x) :=
  (Primrec.nat_lt.computablePred.decide.comp (hf.pair hg)).computablePred
@[fun_prop] lemma ca_ratLe {f g : α → ℚ} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun x=>f x≤g x) :=
  (primrec_ratLe.computablePred.decide.comp (hf.pair hg)).computablePred
@[fun_prop] lemma ca_ratLt {f g : α → ℚ} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun x=>f x<g x) :=
  (primrec_ratLt.computablePred.decide.comp (hf.pair hg)).computablePred

example : Computable (fun p : ℕ × ℚ=> (p.1:ℚ) * (p.2+1)^p.1) := by fun_prop
example : ComputablePred (fun p : ℕ × ℚ=> p.1<2 ∧ (p.1:ℚ)*p.2<4) := by fun_prop
end MinUncut.Preprocess

end
namespace MinUncut.Preprocess
variable {α β : Type} [Primcodable α] [Primcodable β]

lemma c_rangeMap {f : α → ℕ → β} (hf : Computable₂ f) :
    Computable₂ (fun a n => (List.range n).map (f a)) := by
  have hh := Computable.nat_rec (α:=α × ℕ) (σ:=List β) Computable.snd
    (Computable.const [])
    (Computable.list_concat.comp
      (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))).to₂
  exact hh.of_eq (by
    intro p
    induction p.2 with
    | zero => rfl
    | succ n ih => simp only [List.range_succ,List.map_append,List.map_singleton,ih])

@[fun_prop] lemma ca_range {f : α → ℕ} (hf : Computable f) :
    Computable (fun a=>List.range (f a)) := Primrec.list_range.to_comp.comp hf
@[fun_prop] lemma ca_sum {f : α → List ℕ} (hf : Computable f) :
    Computable (fun a=>(f a).sum) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).to_comp.comp hf

lemma c_boundedSum {f : α → ℕ → ℕ} {n : α → ℕ}
    (hf : Computable₂ f) (hn : Computable n) :
    Computable (fun a=>((List.range (n a)).map (f a)).sum) :=
  ca_sum ((c_rangeMap hf).comp Computable.id hn)

end MinUncut.Preprocess

end OAI
