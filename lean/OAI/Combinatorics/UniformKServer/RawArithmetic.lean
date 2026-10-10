import Mathlib

namespace OAI

                                    
section

/-! A primitive-recursive nonnegative rational presentation for the uniform
finite certificate search. Denominators are stored minus one, so every bit
string denotes a valid nonnegative rational; there is no division oracle. -/
namespace UniformKServer.RawArithmetic
abbrev Q := ℕ × ℕ

def value (a : Q) : ℚ := (a.1:ℚ)/(a.2+1)
def natural (n : ℕ) : Q := (n,0)
def add (a b : Q) : Q := (a.1*(b.2+1)+b.1*(a.2+1),(a.2+1)*(b.2+1)-1)
def mul (a b : Q) : Q := (a.1*b.1,(a.2+1)*(b.2+1)-1)
def divide (a : Q) (b : ℕ) : Q := (a.1,(a.2+1)*(b+1)-1)
def le (a b : Q) : Prop := a.1*(b.2+1) ≤ b.1*(a.2+1)
instance (a b : Q) : Decidable (le a b) := inferInstanceAs (Decidable (_≤_))

theorem denominator (a b : ℕ) : (a+1)*(b+1)-1+1=(a+1)*(b+1) := by
  have h : 1≤(a+1)*(b+1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  omega

@[simp] theorem value_natural (n : ℕ) : value (natural n) = n := by simp [value,natural]
theorem value_nonneg (a : Q) : 0≤value a := by unfold value;positivity
@[simp] theorem value_add (a b : Q) : value (add a b)=value a+value b := by
  have ha : (a.2:ℚ)+1≠0 := by positivity
  have hb : (b.2:ℚ)+1≠0 := by positivity
  simp only [value,add,← Nat.cast_one (R:=ℚ),← Nat.cast_add,denominator,Nat.cast_mul]
  push_cast
  field_simp

@[simp] theorem value_mul (a b : Q) : value (mul a b)=value a*value b := by
  simp only [value,mul,← Nat.cast_one (R:=ℚ),← Nat.cast_add,denominator,Nat.cast_mul]
  ring

@[simp] theorem value_divide (a : Q) (b : ℕ) : value (divide a b)=value a/(b+1) := by
  simp only [value,divide,← Nat.cast_one (R:=ℚ),← Nat.cast_add,denominator,Nat.cast_mul]
  ring

theorem le_iff (a b : Q) : le a b ↔ value a≤value b := by
  unfold le value
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast

theorem eq_present (a : ℚ) (ha : 0≤a) : value (a.num.natAbs,a.den-1)=a := by
  have hd : a.den-1+1=a.den := by have:=a.pos; omega
  unfold value
  rw [←Nat.cast_one (R:=ℚ),←Nat.cast_add,hd]
  have hn : (a.num.natAbs:ℚ)=a.num := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ))
      (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ha))
  rw [hn,Rat.num_div_den]

open Primrec

theorem primitive_natural : Primrec natural := pair .id (const 0)
theorem primitive_add : Primrec₂ add := by
  unfold add
  exact pair (nat_add.comp (nat_mul.comp (fst.comp fst) (succ.comp (snd.comp snd)))
    (nat_mul.comp (fst.comp snd) (succ.comp (snd.comp fst))))
    (nat_sub.comp (nat_mul.comp (succ.comp (snd.comp fst)) (succ.comp (snd.comp snd))) (const 1))
theorem primitive_mul : Primrec₂ mul := by
  unfold mul
  exact pair (nat_mul.comp (fst.comp fst) (fst.comp snd))
    (nat_sub.comp (nat_mul.comp (succ.comp (snd.comp fst)) (succ.comp (snd.comp snd))) (const 1))
theorem primitive_divide : Primrec₂ divide := by
  unfold divide
  exact pair (fst.comp fst)
    (nat_sub.comp (nat_mul.comp (succ.comp (snd.comp fst)) (succ.comp snd)) (const 1))
theorem primitive_le : PrimrecRel le := by
  unfold le
  exact nat_le.comp (nat_mul.comp (fst.comp fst) (succ.comp (snd.comp snd)))
    (nat_mul.comp (fst.comp snd) (succ.comp (snd.comp fst)))

end UniformKServer.RawArithmetic

end



end OAI
