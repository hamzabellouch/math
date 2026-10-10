import Mathlib

namespace OAI

/-! Dyadic Laws. -/

noncomputable section



 

 

open scoped BigOperators

namespace Contingency

 

structure DyadicLaw (α : Type*) [Fintype α] where
  bits : ℕ
  count : α → ℕ
  total : ∑ z, count z = 2 ^ bits

namespace DyadicLaw

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

 
def pure [DecidableEq α] (z : α) (R : ℕ := 0) : DyadicLaw α where
  bits := R
  count x := if x = z then 2 ^ R else 0
  total := by simp

 

def bind (p : DyadicLaw α) (q : α → DyadicLaw β) (S : ℕ)
    (hq : ∀ x, (q x).bits = S) : DyadicLaw β where
  bits := p.bits + S
  count y := ∑ x, p.count x * (q x).count y
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, DyadicLaw.total, hq]
    rw [← Finset.sum_mul, p.total, pow_add]

 
def map [DecidableEq β] (f : α → β) (p : DyadicLaw α) : DyadicLaw β :=
  p.bind (fun x => pure (f x)) 0 (fun _ => rfl)

@[simp] theorem map_bits [DecidableEq β] (f : α → β) (p : DyadicLaw α) :
    (p.map f).bits = p.bits := by simp [map, bind]

@[simp] theorem map_count [DecidableEq β] (f : α → β) (p : DyadicLaw α) (y : β) :
    (p.map f).count y = ∑ x, if f x = y then p.count x else 0 := by
  simp only [map, bind, pure, pow_zero, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = y
  · simp [h]
  · simp [h, Ne.symm h]

 
def walk [DecidableEq α] (q : α → DyadicLaw α) (S : ℕ)
    (hq : ∀ x, (q x).bits = S) (x₀ : α) : ℕ → DyadicLaw α
  | 0 => pure x₀
  | t + 1 => (walk q S hq x₀ t).bind q S hq

@[simp] theorem walk_bits [DecidableEq α] (q : α → DyadicLaw α) (S : ℕ)
    (hq : ∀ x, (q x).bits = S) (x₀ : α) (t : ℕ) :
    (walk q S hq x₀ t).bits = t * S := by
  induction t with
  | zero => simp [walk, pure]
  | succ t ih => simp [walk, bind, ih, Nat.succ_mul]

def probability (p : DyadicLaw α) (x : α) : ℚ := p.count x / 2 ^ p.bits

@[simp] theorem probability_nonneg (p : DyadicLaw α) (x : α) :
    0 ≤ p.probability x := by
  unfold probability
  positivity

@[simp] theorem probability_total (p : DyadicLaw α) :
    ∑ x, p.probability x = 1 := by
  unfold probability
  rw [← Finset.sum_div]
  norm_cast
  rw [p.total]
  norm_num

end DyadicLaw

 
def bitWordLaw (r : ℕ) : DyadicLaw (Fin (2 ^ r)) where
  bits := r
  count _ := 1
  total := by simp

 
def roundedOffset (w : ℕ) (hw : 0 < w) (r : ℕ) (z : Fin (2 ^ r)) : Fin w :=
  ⟨w * z.val / 2 ^ r, by
    apply (Nat.div_lt_iff_lt_mul (pow_pos (by omega) _)).mpr
    exact Nat.mul_lt_mul_of_pos_left z.isLt hw⟩

 
def offsetLaw (w : ℕ) (hw : 0 < w) (r : ℕ) : DyadicLaw (Fin w) :=
  (bitWordLaw r).map (roundedOffset w hw r)

 
def offsetNumerator (w r u : ℕ) : ℕ :=
  ((u + 1) * 2 ^ r) ⌈/⌉ w - (u * 2 ^ r) ⌈/⌉ w

theorem offset_preimage (w : ℕ) (hw : 0 < w) (r u : ℕ) (hu : u < w) :
    {z ∈ Finset.range (2 ^ r) | w * z / 2 ^ r = u} =
      Finset.Ico ((u * 2 ^ r) ⌈/⌉ w) (((u + 1) * 2 ^ r) ⌈/⌉ w) := by
  ext z
  have hpow : 0 < 2 ^ r := pow_pos (by omega) _
  have hlo : (u * 2 ^ r) ⌈/⌉ w ≤ z ↔ u ≤ w * z / 2 ^ r := by
    rw [ceilDiv_le_iff_le_mul hw, Nat.le_div_iff_mul_le hpow]
  have hhi : z < ((u + 1) * 2 ^ r) ⌈/⌉ w ↔ w * z / 2 ^ r < u + 1 := by
    rw [lt_iff_not_ge, ceilDiv_le_iff_le_mul hw, not_le,
      Nat.div_lt_iff_lt_mul hpow]
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, hlo, hhi]
  constructor
  · rintro ⟨_, heq⟩
    omega
  · rintro ⟨h1, h2⟩
    have heq : w * z / 2 ^ r = u := by omega
    refine ⟨?_, heq⟩
    have hlt : w * z < w * 2 ^ r :=
      (Nat.div_lt_iff_lt_mul hpow).mp (by omega)
    exact (Nat.mul_lt_mul_left hw).mp hlt

theorem offsetLaw_count (w : ℕ) (hw : 0 < w) (r : ℕ) (u : Fin w) :
    (offsetLaw w hw r).count u = offsetNumerator w r u.val := by
  rw [offsetLaw, DyadicLaw.map_count]
  simp only [bitWordLaw, roundedOffset, Fin.ext_iff]
  rw [Fin.sum_univ_eq_sum_range (fun z : ℕ =>
    if w * z / 2 ^ r = u.val then (1 : ℕ) else 0) (2 ^ r)]
  rw [← Finset.card_filter, offset_preimage w hw r u u.isLt, Nat.card_Ico]
  rfl

 

def stoppedNumerator {α : Type*} [DecidableEq α] (R φ : ℕ) (a : α → ℕ)
    (fallback z : α) : ℕ → ℕ
  | 0 => if z = fallback then 1 else 0
  | J + 1 => a z * 2 ^ (R * J) + φ * stoppedNumerator R φ a fallback z J

theorem stoppedNumerator_total {α : Type*} [Fintype α] [DecidableEq α]
    (R φ : ℕ) (a : α → ℕ) (fallback : α) (ht : (∑ z, a z) + φ = 2 ^ R)
    (J : ℕ) : ∑ z, stoppedNumerator R φ a fallback z J = 2 ^ (R * J) := by
  induction J with
  | zero => simp [stoppedNumerator]
  | succ J ih =>
    simp only [stoppedNumerator, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, ih]
    rw [← add_mul, ht, Nat.mul_succ, pow_add]
    ring

 

def stoppedLaw {α : Type*} [Fintype α] [DecidableEq α]
    (trial : DyadicLaw (Option α)) (fallback : α) (J : ℕ) : DyadicLaw α where
  bits := trial.bits * J
  count z := stoppedNumerator trial.bits (trial.count none)
    (fun z => trial.count (some z)) fallback z J
  total := stoppedNumerator_total _ _ _ _ (by
    have ht := trial.total
    rw [Fintype.sum_option] at ht
    omega) J

 
theorem stoppedNumerator_closed {α : Type*} [DecidableEq α]
    (R φ : ℕ) (a : α → ℕ) (fallback z : α) (J : ℕ) :
    stoppedNumerator R φ a fallback z J =
      (∑ j ∈ Finset.range J, φ ^ j * a z * 2 ^ (R * (J - j - 1))) +
        (if z = fallback then φ ^ J else 0) := by
  induction J with
  | zero => simp [stoppedNumerator]
  | succ J ih =>
    rw [stoppedNumerator, ih, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_cancel]
    have hs : (∑ j ∈ Finset.range J,
        φ ^ (j + 1) * a z * 2 ^ (R * (J + 1 - (j + 1) - 1))) =
        φ * ∑ j ∈ Finset.range J, φ ^ j * a z * 2 ^ (R * (J - j - 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.add_sub_add_right, pow_succ]
      ring
    rw [hs]
    by_cases hz : z = fallback <;> simp [hz, pow_succ] <;> ring

 
def residualNumerator (M R D a : ℕ) : ℤ :=
  (2 : ℤ) ^ (R + D) - M * ((2 : ℤ) ^ D - 1) * a

theorem residual_integers {α : Type*} [Fintype α] (R D : ℕ) (a : α → ℕ)
    (htotal : ∑ z, a z = 2 ^ R)
    (hdom : ∀ z, (Fintype.card α : ℤ) * ((2 : ℤ) ^ D - 1) * a z ≤
      (2 : ℤ) ^ (R + D)) :
    (∀ z, 0 ≤ residualNumerator (Fintype.card α) R D (a z)) ∧
    (∑ z, residualNumerator (Fintype.card α) R D (a z) =
      (Fintype.card α : ℤ) * 2 ^ R) := by
  constructor
  · intro z
    exact sub_nonneg.mpr (hdom z)
  · have ht : ∑ z, (a z : ℤ) = (2 : ℤ) ^ R := by exact_mod_cast htotal
    simp only [residualNumerator, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    rw [ht, pow_add]
    ring

end Contingency

 

 

open scoped BigOperators
namespace Contingency
noncomputable section

structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x,0 ≤ mass x
  total : ∑ x,mass x=1

namespace Law
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] theorem ext {p r : Law α} (h : p.mass=r.mass) : p=r := by cases p; cases r; cases h; rfl

def pure (x : α) : Law α := by
  classical
  exact ⟨fun y => if x=y then 1 else 0,fun y => by split_ifs <;> norm_num,by simp⟩

def bind (p : Law α) (k : α → Law β) : Law β where
  mass y := ∑ x,p.mass x*(k x).mass y
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) ((k x).nonneg y)
  total := by rw [Finset.sum_comm]; simp only [← Finset.mul_sum,Law.total,mul_one]

def map (f : α → β) (p : Law α) : Law β := p.bind (fun x => pure (f x))

def tv (p r : Law α) : ℝ := (∑ x,|p.mass x-r.mass x|)/2

theorem tv_nonneg (p r : Law α) : 0 ≤ p.tv r := by unfold tv; positivity
@[simp] theorem tv_self (p : Law α) : p.tv p=0 := by simp [tv]
theorem tv_symm (p r : Law α) : p.tv r=r.tv p := by simp only [tv,abs_sub_comm]

theorem tv_triangle (p r s : Law α) : p.tv s ≤ p.tv r+r.tv s := by
  unfold tv
  rw [← add_div,← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum fun x _ => abs_sub_le _ _ _

theorem tv_le_one (p r : Law α) : p.tv r ≤ 1 := by
  have h : (∑ x,|p.mass x-r.mass x|) ≤ 2 := by
    calc
      _ ≤ ∑ x,(p.mass x+r.mass x) := Finset.sum_le_sum fun x _ => by
        rw [abs_le]; constructor <;> linarith [p.nonneg x,r.nonneg x]
      _ = 2 := by rw [Finset.sum_add_distrib,p.total,r.total]; norm_num
  unfold tv; linarith

theorem tv_bind_left (p r : Law α) (k : α → Law β) :
    (p.bind k).tv (r.bind k) ≤ p.tv r := by
  unfold tv
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ = ∑ y,|∑ x,(p.mass x-r.mass x)*(k x).mass y| := by
      simp only [bind,sub_mul,Finset.sum_sub_distrib]
    _ ≤ ∑ y,∑ x,|p.mass x-r.mass x| *(k x).mass y := by
      apply Finset.sum_le_sum; intro y _
      have hh := Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun x => (p.mass x-r.mass x)*(k x).mass y)
      simpa only [abs_mul,abs_of_nonneg ((k _).nonneg _)] using hh
    _ = _ := by rw [Finset.sum_comm]; simp only [← Finset.mul_sum,Law.total,mul_one]

theorem tv_bind_right (p : Law α) (k l : α → Law β) :
    (p.bind k).tv (p.bind l) ≤ ∑ x,p.mass x*(k x).tv (l x) := by
  unfold tv
  rw [show (∑ x,p.mass x*((∑ y,|(k x).mass y-(l x).mass y|)/2))=
    (∑ x,∑ y,p.mass x*|(k x).mass y-(l x).mass y|)/2 by simp only [mul_div_assoc,Finset.mul_sum,Finset.sum_div]]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ = ∑ y,|∑ x,p.mass x*((k x).mass y-(l x).mass y)| := by simp only [bind,mul_sub,Finset.sum_sub_distrib]
    _ ≤ ∑ y,∑ x,p.mass x*|(k x).mass y-(l x).mass y| := by
      apply Finset.sum_le_sum; intro y _
      have hh := Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun x => p.mass x*((k x).mass y-(l x).mass y))
      simpa only [abs_mul,abs_of_nonneg (p.nonneg _)] using hh
    _ = _ := Finset.sum_comm

theorem tv_bind_right_bound (p : Law α) (k l : α → Law β) (δ : ℝ)
    (hδ : ∀ x,(k x).tv (l x) ≤ δ) : (p.bind k).tv (p.bind l) ≤ δ := by
  apply (tv_bind_right p k l).trans
  calc
    _ ≤ ∑ x,p.mass x*δ := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hδ x) (p.nonneg x)
    _ = δ := by rw [← Finset.sum_mul,p.total,one_mul]

theorem tv_bind (p r : Law α) (k l : α → Law β) (δ : ℝ)
    (hδ : ∀ x,(k x).tv (l x) ≤ δ) : (p.bind k).tv (r.bind l) ≤ p.tv r+δ := by
  exact (tv_triangle _ (r.bind k) _).trans (add_le_add (tv_bind_left p r k) (tv_bind_right_bound r k l δ hδ))

theorem tv_map (f : α → β) (p r : Law α) : (p.map f).tv (r.map f) ≤ p.tv r :=
  tv_bind_left _ _ _

def first (p : Law (Option α)) (fallback : α) : ℕ → Law α
  | 0 => pure fallback
  | J+1 => p.bind (fun o => match o with | none => first p fallback J | some x => pure x)

 
theorem first_tv (p r : Law (Option α)) (fallback : α) (J : ℕ) :
    (first p fallback J).tv (first r fallback J) ≤ J*p.tv r := by
  induction J with
  | zero => simp [first]
  | succ J ih =>
    have h := tv_bind p r
      (fun o => match o with | none => first p fallback J | some x => pure x)
      (fun o => match o with | none => first r fallback J | some x => pure x)
      (J*p.tv r) (by intro o; cases o; exact ih; simpa only [tv_self] using mul_nonneg (Nat.cast_nonneg J) (tv_nonneg p r))
    simpa only [first,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using h

@[simp] theorem bind_pure_mass (p : Law α) (y : α) : (p.bind pure).mass y=p.mass y := by
  classical
  simp [bind,pure]

theorem first_mass (p : Law (Option α)) (fallback : α) (u : Law α)
    (h : ∀ x,p.mass (some x)=(1-p.mass none)*u.mass x) (J : ℕ) (x : α) :
    (first p fallback J).mass x=(1-p.mass none^J)*u.mass x+p.mass none^J*(pure fallback).mass x := by
  induction J with
  | zero => simp [first]
  | succ J ih =>
    change (∑ o : Option α,p.mass o*(match o with | none => first p fallback J | some y => pure y).mass x)=_
    rw [Fintype.sum_option]
    simp only [h]
    have he : (∑ y,(1-p.mass none)*u.mass y*(pure y).mass x)=(1-p.mass none)*u.mass x := by
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      change (1-p.mass none)*(u.bind pure).mass x=_
      rw [bind_pure_mass]
    rw [he,ih,pow_succ]
    ring

theorem first_ideal_tv (p : Law (Option α)) (fallback : α) (u : Law α)
    (h : ∀ x,p.mass (some x)=(1-p.mass none)*u.mass x) (J : ℕ) :
    (first p fallback J).tv u ≤ p.mass none^J := by
  have he : (first p fallback J).tv u=p.mass none^J*(pure fallback).tv u := by
    unfold tv
    simp only [first_mass p fallback u h J]
    have hh (x) : (1-p.mass none^J)*u.mass x+p.mass none^J*(pure fallback).mass x-u.mass x=
        p.mass none^J*((pure fallback).mass x-u.mass x) := by ring
    simp only [hh,abs_mul,abs_of_nonneg (pow_nonneg (p.nonneg none) J),← Finset.mul_sum]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (tv_le_one (pure fallback) u) (pow_nonneg (p.nonneg none) J)
  simpa only [mul_one] using hh

end Law
end
end Contingency

 

 

open scoped BigOperators
namespace Contingency
noncomputable section
namespace DyadicLaw
variable {α β : Type*} [Fintype α] [Fintype β]
def toLaw (p : DyadicLaw α) : Law α where
  mass x := (p.count x:ℝ)/2^p.bits
  nonneg x := by positivity
  total := by
    rw [← Finset.sum_div]
    have hh : (∑ x,(p.count x:ℝ))=(2:ℝ)^p.bits := by exact_mod_cast p.total
    rw [hh]
    exact div_self (by positivity)

theorem toLaw_bind (p : DyadicLaw α) (k : α → DyadicLaw β) (S : ℕ)
    (hk : ∀ x,(k x).bits=S) : (p.bind k S hk).toLaw=p.toLaw.bind (fun x => (k x).toLaw) := by
  apply Law.ext
  funext y
  simp only [toLaw,bind,Law.bind,Nat.cast_sum,Nat.cast_mul,pow_add,hk,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring
end DyadicLaw

namespace Law

def uniform (α : Type*) [Fintype α] [Nonempty α] : Law α where
  mass _ := 1/Fintype.card α
  nonneg _ := by positivity
  total := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; field_simp

end Law

theorem ceilDiv_error (a w : ℕ) (hw : 0<w) :
    (a:ℝ) ≤ w*(a⌈/⌉w:ℕ) ∧ w*(a⌈/⌉w:ℕ) ≤ (a:ℝ)+w := by
  constructor
  · exact_mod_cast (ceilDiv_le_iff_le_mul hw).mp (le_refl (a⌈/⌉w))
  · have hh : w*(a⌈/⌉w)≤a+w := by
      rw [Nat.ceilDiv_eq_add_pred_div,Nat.mul_comm]
      exact (Nat.div_mul_le_self (a+w-1) w).trans (Nat.sub_le _ _)
    exact_mod_cast hh

theorem offsetNumerator_error (w : ℕ) (hw : 0<w) (r u : ℕ) :
    |(w:ℝ)*offsetNumerator w r u-(2:ℝ)^r| ≤ w := by
  have hmono : (u*2^r)⌈/⌉w ≤ ((u+1)*2^r)⌈/⌉w :=
    (gc_mul_ceilDiv hw).monotone_l (Nat.mul_le_mul_right (2^r) (Nat.le_succ u))
  rw [offsetNumerator,Nat.cast_sub hmono,abs_le]
  have hlo := ceilDiv_error (u*2^r) w hw
  have hhi := ceilDiv_error ((u+1)*2^r) w hw
  push_cast at hlo hhi
  constructor <;> nlinarith only [hlo.1,hlo.2,hhi.1,hhi.2]

theorem offsetLaw_point_error (w : ℕ) (hw : 0<w) (r : ℕ) (u : Fin w) :
    |(offsetLaw w hw r).toLaw.mass u-1/(w:ℝ)| ≤ 1/(2:ℝ)^r := by
  have hw0 : (0:ℝ)<w := by exact_mod_cast hw
  have hQ : (0:ℝ)<2^r := by positivity
  change |((offsetLaw w hw r).count u:ℝ)/(2:ℝ)^((offsetLaw w hw r).bits)-1/(w:ℝ)|≤_
  rw [offsetLaw_count]
  change |(offsetNumerator w r u:ℝ)/(2:ℝ)^r-1/(w:ℝ)|≤_
  calc
    _ = |(w:ℝ)*offsetNumerator w r u-(2:ℝ)^r|/((w:ℝ)*(2:ℝ)^r) := by
      rw [← abs_of_pos (mul_pos hw0 hQ),← abs_div]
      congr 1
      field_simp
    _ ≤ (w:ℝ)/((w:ℝ)*(2:ℝ)^r) := div_le_div_of_nonneg_right (offsetNumerator_error w hw r u) (by positivity)
    _ = _ := by field_simp

theorem offsetLaw_tv (w : ℕ) (hw : 0<w) (r : ℕ) :
    letI : Nonempty (Fin w) := ⟨⟨0,hw⟩⟩
    (offsetLaw w hw r).toLaw.tv (Law.uniform (Fin w)) ≤ (w:ℝ)/(2:ℝ)^r := by
  unfold Law.tv Law.uniform
  simp only [Fintype.card_fin]
  have hh : (∑ u : Fin w,|(offsetLaw w hw r).toLaw.mass u-1/(w:ℝ)|) ≤ (w:ℝ)/(2:ℝ)^r := by
    calc
      _ ≤ ∑ _ : Fin w,1/(2:ℝ)^r := Finset.sum_le_sum fun u _ => offsetLaw_point_error w hw r u
      _ = _ := by simp [div_eq_mul_inv]
  have hn : (0:ℝ)≤(w:ℝ)/(2:ℝ)^r := by positivity
  linarith

 
theorem rounded_offset_accuracy (w h d : ℕ) (hw : 0<w) :
    letI : Nonempty (Fin w) := ⟨⟨0,hw⟩⟩
    (offsetLaw w hw (Nat.clog 2 (w+1)+4*(h+d))).toLaw.tv (Law.uniform (Fin w)) ≤
      (2:ℝ)^(-((4*(h+d):ℕ):ℤ)) := by
  apply (offsetLaw_tv w hw _).trans
  have hh : (w:ℝ) ≤ 2^Nat.clog 2 (w+1) := by
    exact_mod_cast ((Nat.le_succ w).trans (Nat.le_pow_clog (by norm_num) (w+1)))
  rw [pow_add]
  calc
    _ ≤ (2:ℝ)^Nat.clog 2 (w+1)/((2:ℝ)^Nat.clog 2 (w+1)*(2:ℝ)^(4*(h+d))) := by gcongr
    _ = _ := by rw [zpow_neg,zpow_natCast]; field_simp

end
end Contingency

 

 

open scoped BigOperators
namespace Contingency.Law
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i,Fintype (α i)]

def pi (p : ∀ i,Law (α i)) : Law (∀ i,α i) where
  mass x := ∏ i,(p i).mass (x i)
  nonneg x := Finset.prod_nonneg fun i _ => (p i).nonneg (x i)
  total := by
    rw [← Fintype.prod_sum]
    simp only [Law.total,Finset.prod_const_one]

theorem tv_overlap {β : Type*} [Fintype β] (p r : Law β) :
    p.tv r = 1-∑ x,min (p.mass x) (r.mass x) := by
  have hh : (∑ x,|p.mass x-r.mass x|)=2-2*(∑ x,min (p.mass x) (r.mass x)) := by
    calc
      _ = ∑ x,(p.mass x+r.mass x-2*min (p.mass x) (r.mass x)) := by
        apply Finset.sum_congr rfl; intro x _
        rcases le_total (p.mass x) (r.mass x) with h|h
        · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
        · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
      _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,p.total,r.total]; norm_num
  unfold tv; rw [hh]; ring

omit [Fintype ι] in
theorem deficit_prod_le_sum (f : ι → ℝ) (hf : ∀ i,0≤f i ∧ f i≤1) (s : Finset ι) :
    1-∏ i∈s,f i ≤ ∑ i∈s,(1-f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    have hp : (∏ i∈s,f i)≤1 := Finset.prod_le_one₀ (fun index _ => (hf index).1) (fun index _ => (hf index).2)
    have hn := mul_nonneg (by linarith [(hf a).2] : 0≤1-f a) (by linarith : 0≤1-∏ i∈s,f i)
    nlinarith

 
theorem tv_pi (p r : ∀ i,Law (α i)) :
    (pi p).tv (pi r) ≤ ∑ i,(p i).tv (r i) := by
  classical
  have hs : (∏ i,∑ x,min ((p i).mass x) ((r i).mass x)) ≤
      ∑ x,min ((pi p).mass x) ((pi r).mass x) := by
    rw [Fintype.prod_sum]
    apply Finset.sum_le_sum
    intro x _
    apply le_min
    · exact Finset.prod_le_prod₀ (fun index _ => le_min ((p index).nonneg _) ((r index).nonneg _))
        (fun index _ => min_le_left _ _)
    · exact Finset.prod_le_prod₀ (fun index _ => le_min ((p index).nonneg _) ((r index).nonneg _))
        (fun index _ => min_le_right _ _)
  have he (i) : (∑ x,min ((p i).mass x) ((r i).mass x))=1-(p i).tv (r i) := by rw [tv_overlap]; ring
  simp only [he] at hs
  have hb := deficit_prod_le_sum (fun i => 1-(p i).tv (r i)) (fun i =>
    ⟨by linarith [tv_le_one (p i) (r i)],by linarith [tv_nonneg (p i) (r i)]⟩) Finset.univ
  simp only [sub_sub_cancel] at hb
  rw [tv_overlap]
  linarith

variable {β γ : Type*} [Fintype β] [Fintype γ]
def prod (p : Law β) (r : Law γ) : Law (β×γ) where
  mass x := p.mass x.1*r.mass x.2
  nonneg x := mul_nonneg (p.nonneg _) (r.nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp only [← Finset.mul_sum,r.total,mul_one,p.total]

theorem prod_eq_bind (p : Law β) (r : Law γ) : p.prod r=p.bind (fun x => r.map (x,·)) := by
  classical
  apply Law.ext; funext y
  simp only [prod,bind,map,pure,Prod.ext_iff]
  have hh (x : β) : (∑ z : γ,r.mass z*(if x=y.1 ∧ z=y.2 then 1 else 0))=
      if x=y.1 then r.mass y.2 else 0 := by
    by_cases h : x=y.1 <;> simp [h]
  simp only [hh]
  simp

theorem tv_prod (p p' : Law β) (r r' : Law γ) :
    (p.prod r).tv (p'.prod r') ≤ p.tv p'+r.tv r' := by
  rw [prod_eq_bind,prod_eq_bind]
  exact tv_bind p p' _ _ _ (fun x => tv_map (x,·) r r')

end
end Contingency.Law

 

 

open scoped BigOperators
namespace Contingency
noncomputable section
namespace DyadicLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem toLaw_pure [DecidableEq α] (x : α) (R : ℕ) : (pure x R).toLaw=Law.pure x := by
  apply Law.ext; funext y
  by_cases h : x=y
  · subst y; simp [toLaw,pure,Law.pure]
  · simp [toLaw,pure,Law.pure,h,Ne.symm h]

theorem toLaw_map [DecidableEq β] (f : α → β) (p : DyadicLaw α) :
    (p.map f).toLaw=p.toLaw.map f := by
  change (p.bind (fun x => pure (f x)) 0 (fun _ => rfl)).toLaw=p.toLaw.map f
  exact (toLaw_bind p (fun x => pure (f x)) 0 (fun _ => rfl)).trans (by
    simp only [toLaw_pure,Law.map])

def pad (p : DyadicLaw α) (R : ℕ) (hR : p.bits≤R) : DyadicLaw α where
  bits := R
  count x := p.count x*2^(R-p.bits)
  total := by rw [← Finset.sum_mul,p.total,← pow_add,Nat.add_sub_of_le hR]

theorem toLaw_pad (p : DyadicLaw α) (R : ℕ) (hR : p.bits≤R) : (p.pad R hR).toLaw=p.toLaw := by
  apply Law.ext; funext x
  change ((p.count x*2^(R-p.bits):ℕ):ℝ)/(2:ℝ)^R=(p.count x:ℝ)/(2:ℝ)^p.bits
  push_cast
  have he : (2:ℝ)^R=(2:ℝ)^p.bits*(2:ℝ)^(R-p.bits) := by rw [← pow_add,Nat.add_sub_of_le hR]
  rw [he]
  field_simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {γ : ι → Type*} [∀ i,Fintype (γ i)]
def pi (p : ∀ i,DyadicLaw (γ i)) : DyadicLaw (∀ i,γ i) where
  bits := ∑ i,(p i).bits
  count x := ∏ i,(p i).count (x i)
  total := by rw [← Fintype.prod_sum]; simp only [DyadicLaw.total,Finset.prod_pow_eq_pow_sum]

theorem toLaw_pi (p : ∀ i,DyadicLaw (γ i)) : (pi p).toLaw=Law.pi (fun i => (p i).toLaw) := by
  apply Law.ext; funext x
  simp only [toLaw,pi,Law.pi,Nat.cast_prod,Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]

variable [DecidableEq α]
theorem toLaw_walk (q : α → DyadicLaw α) (S : ℕ) (hq : ∀ x,(q x).bits=S) (x₀ : α) :
    ∀ t,(walk q S hq x₀ t).toLaw=Nat.rec (Law.pure x₀) (fun _ p => p.bind (fun x => (q x).toLaw)) t := by
  intro t
  induction t with
  | zero => simp [walk,toLaw_pure]
  | succ t ih => rw [walk,toLaw_bind,ih]

end DyadicLaw

 
theorem stoppedLaw_toLaw {α : Type*} [Fintype α] [DecidableEq α]
    (p : DyadicLaw (Option α)) (fallback : α) (J : ℕ) :
    (stoppedLaw p fallback J).toLaw=Law.first p.toLaw fallback J := by
  apply Law.ext; funext z
  induction J with
  | zero =>
    by_cases h : z=fallback
    · subst z; simp [stoppedLaw,stoppedNumerator,DyadicLaw.toLaw,Law.first,Law.pure]
    · simp [stoppedLaw,stoppedNumerator,DyadicLaw.toLaw,Law.first,Law.pure,h,Ne.symm h]
  | succ J ih =>
    have hr : (Law.first p.toLaw fallback (J+1)).mass z=
        p.toLaw.mass none*(Law.first p.toLaw fallback J).mass z+p.toLaw.mass (some z) := by
      change (∑ o : Option α,p.toLaw.mass o*(match o with | none => Law.first p.toLaw fallback J | some y => Law.pure y).mass z)=_
      rw [Fintype.sum_option]
      simp [Law.pure]
    rw [hr,← ih]
    change ((p.count (some z)*2^(p.bits*J)+p.count none*stoppedNumerator p.bits (p.count none) (fun z => p.count (some z)) fallback z J:ℕ):ℝ)/(2:ℝ)^(p.bits*(J+1))=_
    simp only [DyadicLaw.toLaw,stoppedLaw]
    push_cast
    rw [Nat.mul_succ,pow_add]
    field_simp
    ring

end
end Contingency

 

 

open scoped BigOperators
namespace Contingency
noncomputable section
namespace Law
variable {α : Type*} [Fintype α] {β : α → Type*} [∀ x,Fintype (β x)]

def sigma (p : Law α) (q : ∀ x, Law (β x)) : Law (Sigma β) where
  mass z := p.mass z.1 * (q z.1).mass z.2
  nonneg z := mul_nonneg (p.nonneg _) ((q _).nonneg _)
  total := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, (q _).total, mul_one]
    exact p.total

theorem sigma_eq_bind (p : Law α) (q : ∀ x,Law (β x)) :
    p.sigma q=p.bind (fun x => (q x).map (Sigma.mk x)) := by
  classical
  let : DecidableEq (Sigma β) := fun _ _ => Classical.propDecidable _
  apply Law.ext; funext ⟨x,y⟩
  simp only [sigma,bind,map,pure]
  have hh (z : α) : (∑ w : β z, (q z).mass w * (if Sigma.mk z w=Sigma.mk x y then 1 else 0))=
      if h : z=x then (q x).mass y else 0 := by
    by_cases h : z=x
    · subst z; simp
    · have hn (w : β z) : Sigma.mk z w ≠ Sigma.mk x y := by intro he; exact h (congrArg Sigma.fst he)
      simp [h,hn]
  change p.mass x * (q x).mass y = ∑ z, p.mass z * (∑ w : β z, (q z).mass w * (if Sigma.mk z w = Sigma.mk x y then 1 else 0))
  simp_rw [hh]
  simp

theorem tv_sigma (p p' : Law α) (q q' : ∀ x,Law (β x)) (δ : ℝ)
    (hq : ∀ x,(q x).tv (q' x) ≤ δ) :
    (p.sigma q).tv (p'.sigma q') ≤ p.tv p'+δ := by
  rw [sigma_eq_bind,sigma_eq_bind]
  exact tv_bind p p' _ _ δ (fun x => (tv_map _ _ _).trans (hq x))

end Law
namespace DyadicLaw
variable {α : Type*} [Fintype α] {β : α → Type*} [∀ x,Fintype (β x)]

def sigma (p : DyadicLaw α) (q : ∀ x,DyadicLaw (β x)) (S : ℕ) (hS : ∀ x,(q x).bits=S) : DyadicLaw (Sigma β) where
  bits := p.bits+S
  count z := p.count z.1*(q z.1).count z.2
  total := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, (q _).total, hS]
    rw [← Finset.sum_mul,p.total,pow_add]

theorem sigma_bits (p : DyadicLaw α) (q : ∀ x,DyadicLaw (β x)) (S : ℕ) (hS : ∀ x,(q x).bits=S) :
    (p.sigma q S hS).bits=p.bits+S := rfl

theorem toLaw_sigma (p : DyadicLaw α) (q : ∀ x,DyadicLaw (β x)) (S : ℕ) (hS : ∀ x,(q x).bits=S) :
    (p.sigma q S hS).toLaw=p.toLaw.sigma (fun x => (q x).toLaw) := by
  apply Law.ext; funext z
  simp only [sigma,toLaw,Law.sigma,Nat.cast_mul,pow_add,hS]
  ring

end DyadicLaw
end
end Contingency

end

end OAI
