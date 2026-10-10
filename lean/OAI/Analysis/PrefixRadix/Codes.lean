import Mathlib
import OAI.Computability.Interspersed.Stacks

namespace OAI

/-! Gapped radix systems and injective infinite stack codes. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
namespace Radix
structure System (A : Type*) where
  base : ℝ
  base_ge_two : 2 ≤ base
  digit : A → ℝ
  digit_nonneg : ∀ a, 0 ≤ digit a
  digit_le : ∀ a, digit a ≤ base - 2
  digit_gap : ∀ a b, a ≠ b → 2 ≤ |digit a - digit b|

namespace System

variable {A : Type*} (C : System A)

def rate : ℝ := C.base⁻¹

theorem base_pos : 0 < C.base := lt_of_lt_of_le (by norm_num) C.base_ge_two

theorem rate_pos : 0 < C.rate := inv_pos.mpr C.base_pos

theorem rate_lt_one : C.rate < 1 :=
  (inv_lt_one₀ C.base_pos).2 (lt_of_lt_of_le (by norm_num) C.base_ge_two)

def code (L : Interspersed.Stack A) : ℝ :=
  (∑' n : ℕ, C.digit (L n) * C.rate ^ n) / C.base

theorem summable_digits (L : Interspersed.Stack A) :
    Summable (fun n : ℕ => C.digit (L n) * C.rate ^ n) := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (C.digit_nonneg _) (pow_nonneg C.rate_pos.le _))
    (fun n => mul_le_mul_of_nonneg_right ?_ (pow_nonneg C.rate_pos.le n))
    ((summable_geometric_of_lt_one C.rate_pos.le C.rate_lt_one).mul_left (C.base - 1))
  have h := C.digit_le (L n)
  linarith

 
theorem code_mem_unit (L : Interspersed.Stack A) : C.code L ∈ Set.Icc (0 : ℝ) 1 := by
  have hb := C.base_pos
  have hbm : C.base - 1 ≠ 0 := ne_of_gt (by linarith [C.base_ge_two])
  have hb0 := ne_of_gt hb
  have hgeom := summable_geometric_of_lt_one C.rate_pos.le C.rate_lt_one
  have hle := Summable.tsum_le_tsum
    (g := fun n : ℕ => (C.base - 1) * C.rate ^ n)
    (fun n => mul_le_mul_of_nonneg_right
      (show C.digit (L n) ≤ C.base - 1 by linarith [C.digit_le (L n)])
      (pow_nonneg C.rate_pos.le n)) (C.summable_digits L) (hgeom.mul_left (C.base - 1))
  rw [tsum_mul_left, tsum_geometric_of_lt_one C.rate_pos.le C.rate_lt_one] at hle
  have htotal : (C.base - 1) * (1 - C.rate)⁻¹ = C.base := by
    dsimp [rate]
    field_simp
  constructor
  · exact div_nonneg (tsum_nonneg fun n =>
      mul_nonneg (C.digit_nonneg _) (pow_nonneg C.rate_pos.le n)) hb.le
  · change (∑' n : ℕ, C.digit (L n) * C.rate ^ n) / C.base ≤ 1
    exact (div_le_iff₀ hb).2 (by simpa only [htotal, one_mul] using hle)

 
theorem code_push (a : A) (L : Interspersed.Stack A) :
    C.code (Interspersed.push a L) = (C.digit a + C.code L) / C.base := by
  unfold code
  rw [(C.summable_digits (Interspersed.push a L)).tsum_eq_zero_add]
  simp only [Interspersed.push_zero, Interspersed.push_succ, pow_zero, mul_one]
  have hfun : (fun n : ℕ => C.digit (L n) * C.rate ^ (n + 1)) =
      (fun n : ℕ => C.rate * (C.digit (L n) * C.rate ^ n)) := by
    funext n
    rw [pow_succ]
    ring
  rw [hfun, tsum_mul_left]
  simp only [rate, div_eq_mul_inv]
  ring

 
theorem code_constant (a : A) :
    C.code (fun _ => a) = C.digit a / (C.base - 1) := by
  unfold code
  rw [tsum_mul_left, tsum_geometric_of_lt_one C.rate_pos.le C.rate_lt_one]
  dsimp only [rate]
  have hb := ne_of_gt C.base_pos
  have hbm : C.base - 1 ≠ 0 := ne_of_gt (by linarith [C.base_ge_two])
  field_simp

 

theorem first_letter_gap {a b : A} (hab : a ≠ b) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    C.rate ≤ |(C.digit a + x) / C.base - (C.digit b + y) / C.base| := by
  have hb := C.base_pos
  have hg := C.digit_gap a b hab
  rcases le_total (C.digit a) (C.digit b) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hg
    have hsep : 1 ≤ (C.digit b + y) - (C.digit a + x) := by
      linarith [hx.2, hy.1]
    have hbound := div_le_div_of_nonneg_right hsep hb.le
    rw [sub_div] at hbound
    calc
      C.rate ≤ (C.digit b + y) / C.base - (C.digit a + x) / C.base := by
        simpa [rate] using hbound
      _ ≤ |(C.digit b + y) / C.base - (C.digit a + x) / C.base| := le_abs_self _
      _ = _ := abs_sub_comm _ _
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hg
    have hsep : 1 ≤ (C.digit a + x) - (C.digit b + y) := by
      linarith [hx.1, hy.2]
    have hbound := div_le_div_of_nonneg_right hsep hb.le
    rw [sub_div] at hbound
    exact (show C.rate ≤ (C.digit a + x) / C.base - (C.digit b + y) / C.base by
      simpa [rate] using hbound).trans (le_abs_self _)

theorem code_push_inj {a b : A} {L R : Interspersed.Stack A}
    (h : C.code (Interspersed.push a L) = C.code (Interspersed.push b R)) :
    a = b ∧ C.code L = C.code R := by
  rw [C.code_push, C.code_push] at h
  have hab : a = b := by
    by_contra hab
    have hg := C.first_letter_gap hab (C.code_mem_unit L) (C.code_mem_unit R)
    rw [h, sub_self, abs_zero] at hg
    exact (not_le_of_gt C.rate_pos) hg
  subst b
  exact ⟨rfl, add_left_cancel ((div_left_inj' (ne_of_gt C.base_pos)).mp h)⟩

 

theorem head_tail_of_code {L R : Interspersed.Stack A} (h : C.code L = C.code R) :
    L 0 = R 0 ∧ C.code (fun n => L (n + 1)) = C.code (fun n => R (n + 1)) := by
  have he (S : Interspersed.Stack A) :
      Interspersed.push (S 0) (fun n => S (n + 1)) = S := by
    funext n
    cases n <;> rfl
  apply C.code_push_inj
  simpa only [he] using h

 

theorem code_injective : Function.Injective C.code := by
  have recover : ∀ n, ∀ {L R : Interspersed.Stack A}, C.code L = C.code R → L n = R n := by
    intro n
    induction n with
    | zero => intro L R h; exact (C.head_tail_of_code h).1
    | succ n ih =>
      intro L R h
      exact ih (C.head_tail_of_code h).2
  intro L R h
  funext n
  exact recover n h
end System
end Radix
end PrefixFlows
end

end OAI
